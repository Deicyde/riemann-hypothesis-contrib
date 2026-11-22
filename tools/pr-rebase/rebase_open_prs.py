#!/usr/bin/env python3
"""Rebase pinned public RH PRs in isolation, preserving original Git authors.

Only publishes new preparation/checkpoint/report branches in Jack's fork.
Never updates contributors' branches, merges PRs, executes PR code or builds Lean.
Conflicts remain explicit; no blanket ours/theirs conflict policy is used.
"""
import base64
import collections
import difflib
import json
import os
import re
from pathlib import Path
import subprocess
import sys
import time

UPSTREAM = 'https://github.com/leanprover-community/riemann-hypothesis.git'
OWN = 'https://github.com/Deicyde/riemann-hypothesis-contrib.git'
HERE = Path(__file__).resolve().parent
SNAPSHOT = json.loads((HERE / 'snapshot.json').read_text())
BASE = SNAPSHOT['base']
TAG = BASE[:10]
ROOT = Path(os.environ.get('RUNNER_TEMP', '/tmp')) / ('rh-rebase-' + TAG)
REPO = ROOT / 'repo'
OUT = ROOT / 'results'
ENV = os.environ.copy()
ENV.update(GIT_TERMINAL_PROMPT='0', GIT_EDITOR='true', GIT_SEQUENCE_EDITOR='true',
           GIT_COMMITTER_NAME='github-actions[bot]',
           GIT_COMMITTER_EMAIL='41898282+github-actions[bot]@users.noreply.github.com')
if ENV.get('GH_TOKEN'):
    auth = base64.b64encode(('x-access-token:' + ENV['GH_TOKEN']).encode()).decode()
    ENV.update(GIT_CONFIG_COUNT='1', GIT_CONFIG_KEY_0='http.https://github.com/.extraheader',
               GIT_CONFIG_VALUE_0='AUTHORIZATION: basic ' + auth)


def git(*args, check=True, input=None, timeout=900):
    result = subprocess.run(['git', '-c', 'core.hooksPath=/dev/null', '-c',
                             'commit.gpgsign=false', '-C', str(REPO), *args],
                            input=input, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            text=True, env=ENV, timeout=timeout)
    if check and result.returncode:
        raise RuntimeError('git ' + args[0] + ': ' + result.stderr[-4000:])
    return result


def value(*args):
    return git(*args).stdout.strip()


def publish_ref(sha, branch):
    current = git('ls-remote', OWN, 'refs/heads/' + branch).stdout.split()
    if current:
        if current[0] != sha:
            # Each run has distinct branch names, so existing refs must match exactly.
            raise RuntimeError('Preparation ref already exists with another head: ' + branch)
        return
    git('push', OWN, sha + ':refs/heads/' + branch)


def conflict_details():
    entries = collections.defaultdict(dict)
    for row in git('ls-files', '-u', '-z').stdout.split('\0'):
        if not row:
            continue
        meta, path = row.split('\t', 1)
        mode, sha, stage = meta.split()
        entries[path][stage] = sha
    types = collections.Counter(','.join(sorted(v)) for v in entries.values())
    return {'conflict_count': len(entries), 'stage_types': dict(types),
            'conflicts': [{'path': k, 'stages': v} for k, v in list(entries.items())[:200]],
            'conflict_list_truncated': len(entries) > 200}


def replay_line_deletions(base, ours, theirs):
    """Carry unambiguous declaration-deletion ranges through the compiler port."""
    b, o, t = base.splitlines(keepends=True), ours.splitlines(keepends=True), theirs.splitlines(keepends=True)
    mask = [False] * len(b)
    for tag, a, z, _, _ in difflib.SequenceMatcher(None, b, t, autojunk=len(b)>3000).get_opcodes():
        if tag == 'delete':
            mask[a:z] = [True] * (z-a)
    if not any(mask):
        return None
    prefix = [0]
    for remove in mask:
        prefix.append(prefix[-1] + int(remove))
    out = []
    for tag, a, z, c, d in difflib.SequenceMatcher(None, b, o, autojunk=len(b)>3000).get_opcodes():
        if tag == 'equal':
            out.extend(o[c+i-a] for i in range(a,z) if not mask[i])
        elif tag == 'delete':
            continue
        elif tag == 'insert':
            if not (0<a<len(mask) and mask[a-1] and mask[a]):
                out.extend(o[c:d])
        else:
            removed = prefix[z] - prefix[a]
            if removed == z-a:
                continue
            if removed:
                return None  # A retained declaration overlaps a port rewrite: review separately.
            out.extend(o[c:d])
    return ''.join(line for i,line in enumerate(b) if not mask[i]), ''.join(out)


def replay_generated_cleanup(number, base, ours, theirs):
    """Replay restricted cleanup operations without restoring pre-port proof bodies."""
    b, t = base.splitlines(True), theirs.splitlines(True)
    edits = [(b[a:z],t[c:d]) for kind,a,z,c,d in
             difflib.SequenceMatcher(None,b,t,autojunk=False).get_opcodes() if kind!='equal']
    if number in (4,9):
        old_imports, new_imports, removed_options = set(), [], set()
        for old,new in edits:
            for lines,is_old in ((old,True),(new,False)):
                for line in lines:
                    if not line.strip():
                        continue
                    m = re.fullmatch(r'import\s+([\w.]+)\s*\n?',line)
                    if m:
                        if is_old: old_imports.add(m[1])
                        else: new_imports.append(m[1])
                    elif number==9 and is_old and re.fullmatch(r'set_option (?:synthInstance\.)?maxHeartbeats \d+(?: in)?\s*\n?',line):
                        removed_options.add(line.strip())
                    else:
                        return None
        if number==9 and new_imports:
            return None
        retained=set(new_imports)
        lines=[]
        for line in ours.splitlines(True):
            m=re.fullmatch(r'import\s+([\w.]+)\s*\n?',line)
            if m and m[1] in old_imports-retained:
                continue
            if line.strip() in removed_options:
                continue
            lines.append(line)
        existing={m[1] for line in lines if (m:=re.fullmatch(r'import\s+([\w.]+)\s*\n?',line))}
        additions=list(dict.fromkeys(m for m in new_imports if m not in existing))
        if any(not (REPO/'src'/Path(*m.split('.'))).with_suffix('.lean').exists()
               for m in additions if m!='Mathlib' and not m.startswith('Mathlib.')):
            return None
        last=max((i for i,line in enumerate(lines) if line.startswith('import ')),default=-1)
        if last<0: return None
        lines[last+1:last+1]=['import '+m+'\n' for m in additions]
        return ''.join(lines)
    if number==10:
        out=ours
        for old,new in edits:
            if len(old)!=1 or len(new)!=1:
                return None
            pattern=r'(\s*)first \| exact @([\w.\'₀-₉]+) \| exact \2 \| \(intros; apply \2 <;> assumption\)\s*'
            m=re.fullmatch(pattern,old[0])
            if m and new[0].strip()=='exact @'+m[2]:
                out=out.replace(old[0],new[0])
            else:
                def simp_names(line):
                    m=re.fullmatch(r'\s*simp(?: \[([\w.\', ]+)\])?\s*',line)
                    return None if not m else [s.strip() for s in (m[1] or '').split(',') if s.strip()]
                before,after=simp_names(old[0]),simp_names(new[0])
                if before is None or after is None or not set(after)<set(before):
                    return None
                out=out.replace(old[0],new[0])
        return out
    return None


def resolve_module_conflicts(number):
    """Replay edits through the known module-header conversion, preserving proof edits."""
    entries = collections.defaultdict(dict)
    for row in git('ls-files', '-u', '-z').stdout.split('\0'):
        if row:
            meta, path = row.split('\t', 1)
            mode, sha, stage = meta.split()
            entries[path][stage] = sha
    resolved = []
    pruning = (number in (55,58,61,67) and
               git('rev-parse', 'REBASE_HEAD', check=False).stdout.strip()
               == 'a7016a34bb7e84e8f031c2179bd71cb9c20f2517')
    with subprocess.Popen(['git', '-C', str(REPO), 'cat-file', '--batch'],
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                          stderr=subprocess.DEVNULL, env=ENV) as reader:
        def read_blob(sha):
            reader.stdin.write((sha + '\n').encode())
            reader.stdin.flush()
            header = reader.stdout.readline().split()
            if len(header) != 3 or header[1] != b'blob':
                raise RuntimeError('Could not read conflict blob ' + sha)
            source = reader.stdout.read(int(header[2]))
            if reader.stdout.read(1) != b'\n':
                raise RuntimeError('Malformed blob stream')
            return source.decode('utf-8')
        for path, stages in entries.items():
            if not path.endswith('.lean') or number in (44, 63, 85):
                continue
            if set(stages) == {'1', '3'}:
                # The port pruned this module. Do not resurrect edits to the old dead file.
                (REPO / path).unlink(missing_ok=True)
                resolved.append({'path': path, 'reason': 'retain-main-pruning'})
                continue
            if set(stages) == {'1', '2'}:
                # Preserve this PR's intentional file deletion; validate imports after replay.
                (REPO / path).unlink(missing_ok=True)
                resolved.append({'path': path, 'reason': 'retain-PR-deletion'})
                continue
            if set(stages) != {'1', '2', '3'}:
                continue
            blobs = {stage: read_blob(sha) for stage, sha in stages.items()}
            ours = blobs['2']
            if not ours.startswith('module\n') or '@[expose] public section' not in ours:
                continue
            if any(re.match(r'^import\s', line) for line in ours.splitlines()):
                continue  # A privately imported module requires a separate visibility review.
            def normalize(source):
                source = re.sub(r'\Amodule\n', '', source)
                source = re.sub(r'^public import ', 'import ', source, flags=re.M)
                source = re.sub(r'^@\[expose\] public section\n', '', source, flags=re.M)
                source = re.sub(r'^(import[^\n]*\n)(?:[ \t]*\n)+', r'\1\n', source, flags=re.M)
                return source.lstrip('\n')
            temporary = ROOT / 'merge-inputs'
            temporary.mkdir(exist_ok=True)
            paths = []
            normalized = {stage: normalize(blobs[stage]) for stage in ['2','1','3']}
            cleanup = replay_generated_cleanup(number, normalized['1'],normalized['2'],normalized['3'])
            if cleanup is not None:
                lines=cleanup.splitlines(True)
                imports=[i for i,line in enumerate(lines) if line.startswith('import ')]
                if imports:
                    for i in imports: lines[i]='public '+lines[i]
                    lines.insert(imports[-1]+1,'\n@[expose] public section\n')
                    (REPO/path).write_text(('module\n\n'+''.join(lines)).rstrip()+'\n')
                    resolved.append({'path':path,'reason':'replay-restricted-cleanup-preserving-main-proof-repairs'})
                    continue
            deletion_replay = replay_line_deletions(normalized['1'], normalized['2'], normalized['3']) if pruning else None
            if deletion_replay:
                normalized['1'], normalized['2'] = deletion_replay
            for stage in ['2', '1', '3']:
                f = temporary / stage
                f.write_text(normalized[stage])
                paths.append(str(f))
            merged = subprocess.run(['git', 'merge-file', '-p', *paths],
                                    capture_output=True, text=True)
            if merged.returncode:
                continue
            lines = merged.stdout.splitlines(keepends=True)
            imports = [i for i, line in enumerate(lines) if re.match(r'^import\s', line)]
            if not imports:
                continue
            for i in imports:
                lines[i] = 'public ' + lines[i]
            lines.insert(imports[-1] + 1, '\n@[expose] public section\n')
            (REPO / path).write_text('module\n\n' + ''.join(lines))
            resolved.append({'path': path, 'reason': 'replay-deletion-ranges-through-port' if deletion_replay
                             else 'three-way-replay-through-module-header'})
        reader.stdin.close()
        reader.wait()
    if resolved:
        pathspec = ROOT / 'resolved-paths.nul'
        pathspec.write_bytes(('\0'.join(x['path'] for x in resolved) + '\0').encode())
        git('add', '-A', '--pathspec-from-file=' + str(pathspec), '--pathspec-file-nul')
    return resolved


def resolve_reviewed_ports(number):
    config = HERE / 'reviewed-ports.json'
    if not config.exists():
        return []
    reviewed = json.loads(config.read_text())
    paths = reviewed['prs'].get(str(number), [])
    if not paths:
        return []
    applying = git('rev-parse', 'REBASE_HEAD', check=False).stdout.strip()
    if number == 82 and applying != 'd4fa3841d45d222ce2c4a7f7c73d96a78cf04c55':
        return []
    unmerged = set(git('diff', '--name-only', '--diff-filter=U').stdout.splitlines())
    resolved = []
    for path in paths:
        if path not in unmerged and number not in (74, 82):
            continue
        # These full-file ports are valid only while main still has the reviewed release versions.
        main = git('rev-parse', BASE + ':' + path, check=False)
        release = git('rev-parse', '2e43e1406f4398c615e1e527eeb3334600726cc4:' + path, check=False)
        if main.returncode != release.returncode or (not main.returncode and main.stdout != release.stdout):
            continue
        source = git('show', reviewed['reference'] + ':' + path, check=False)
        if source.returncode:
            continue
        target = REPO / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(source.stdout)
        git('add', '--', path)
        resolved.append({'path': path, 'reason': 'reuse-reviewed-Lean-4.36-port-from-PR91'})
    return resolved


def resolve_manual_ports(number):
    config = HERE / 'manual-resolutions.json'
    if not config.exists():
        return []
    entry = json.loads(config.read_text())['prs'].get(str(number))
    entries = entry if isinstance(entry, list) else [entry]
    applying = value('rev-parse', 'REBASE_HEAD')
    entry = next((e for e in entries if e and e['commit'] == applying), None)
    if not entry:
        return []
    unmerged = set(git('diff', '--name-only', '--diff-filter=U').stdout.splitlines())
    resolved = []
    for f in entry['files']:
        if f['path'] not in unmerged and not (f.get('added') or f.get('restore_main')):
            continue
        prefix = BASE + ':' if f.get('restore_main') else (':' if f.get('added') else ':2:')
        ours = git('rev-parse', prefix + f['path'], check=False)
        if ours.returncode or ours.stdout.strip() != f['ours']:
            continue
        (REPO / f['path']).write_text((HERE / f['resolution']).read_text())
        git('add', '--', f['path'])
        resolved.append({'path': f['path'], 'reason': 'manually-reviewed-Lean-4.36-API-adaptation'})
    return resolved


def resolve_deprecated_identifiers(number):
    if number != 33:
        return []
    result = []
    names = git('diff', '--name-only', '--diff-filter=U').stdout.splitlines()
    token = r"[\w']+(?:\.[\w']+)*|[^\s]"
    identifier = r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*"
    for path in names:
        blobs = [git('show', ':' + stage + ':' + path, check=False) for stage in ['1','2','3']]
        if any(b.returncode for b in blobs):
            continue
        base, ours, theirs = (b.stdout for b in blobs)
        oldlines, newlines = base.splitlines(), theirs.splitlines()
        changes = {}
        valid = True
        for tag, a, b, c, d in difflib.SequenceMatcher(None, oldlines, newlines, autojunk=False).get_opcodes():
            if tag == 'equal':
                continue
            if tag != 'replace' or b-a != d-c:
                if any(line.strip() for line in oldlines[a:b] + newlines[c:d]):
                    valid = False
                continue
            for left, right in zip(oldlines[a:b], newlines[c:d]):
                x, y = re.findall(token, left), re.findall(token, right)
                for kind, i, j, k, l in difflib.SequenceMatcher(None, x, y, autojunk=False).get_opcodes():
                    if kind == 'equal':
                        continue
                    if kind != 'replace' or j-i != l-k:
                        valid = False
                        continue
                    for old, new in zip(x[i:j], y[k:l]):
                        if not re.fullmatch(identifier, old) or not re.fullmatch(identifier, new):
                            valid = False
                            continue
                        if old in changes and changes[old] != new:
                            valid = False
                        changes[old] = new
        if not valid or not changes:
            continue
        def replace(match):
            name = match[0]
            if name in changes:
                return changes[name]
            if name.startswith('_root_.') and name[7:] in changes:
                return '_root_.' + changes[name[7:]]
            for old, new in changes.items():
                if '.' not in old and name.endswith('.' + old):
                    prefix = name[:-(len(old)+1)]
                    if '.' not in new:
                        return prefix + '.' + new
                    if prefix == new.rsplit('.', 1)[0]:
                        return new
            return name
        source = re.sub(r"[\w']+(?:\.[\w']+)*", replace, ours)
        (REPO / path).write_text(source.rstrip() + '\n')
        result.append({'path': path, 'reason': 'replay-only-deprecated-identifier-renames',
                       'identifier_changes': changes})
    if result:
        pathspec = ROOT / 'identifier-paths.nul'
        pathspec.write_bytes(('\0'.join(x['path'] for x in result) + '\0').encode())
        git('add', '-A', '--pathspec-from-file=' + str(pathspec), '--pathspec-file-nul')
    return result


def import_check():
    names = value('ls-tree', '-r', '--name-only', 'HEAD', '--', 'src').splitlines()
    modules = {p[4:-5].replace('/', '.') for p in names if p.endswith('.lean')}
    roots = {p.split('.')[0] for p in modules} | {'BuildAid', 'CompanionTheory', 'Development', 'Formalism', 'GroundTheory', 'Lemmata', 'PositivityTheory', 'ReciprocityTheory', 'Supplements'}
    missing = []
    edges = {m:set() for m in modules}
    proc = subprocess.Popen(['git', '-C', str(REPO), 'grep', '-n', '-E',
                             '^([[:space:]]*(public|meta))*[[:space:]]*import[[:space:]]',
                             'HEAD', '--', 'src'], stdout=subprocess.PIPE,
                            stderr=subprocess.DEVNULL, text=True, env=ENV)
    for line in proc.stdout:
        try:
            _, path, number, source = line.rstrip('\n').split(':', 3)
        except ValueError:
            continue
        match = re.match(r'\s*(?:(?:public|meta)\s+)*import\s+(.+)', source)
        if match:
            for name in match[1].split('--')[0].split():
                if name.split('.')[0] in roots and name not in modules:
                    missing.append({'path': path, 'line': number, 'module': name})
                if name in modules:
                    module = path[4:-5].replace('/', '.')
                    if module in edges: edges[module].add(name)
    proc.wait()
    if proc.returncode not in (0, 1):
        raise RuntimeError('Import scan failed')
    reverse = collections.defaultdict(list)
    counts = {m:len(deps) for m,deps in edges.items()}
    for module,deps in edges.items():
        for dependency in deps: reverse[dependency].append(module)
    queue=collections.deque(m for m,n in counts.items() if not n)
    while queue:
        for dependent in reverse[queue.popleft()]:
            counts[dependent]-=1
            if not counts[dependent]: queue.append(dependent)
    remaining={m for m,n in counts.items() if n}
    cycle=[]
    if remaining:
        current=next(iter(remaining)); seen={}; chain=[]
        while current not in seen:
            seen[current]=len(chain);chain.append(current)
            current=next(d for d in edges[current] if d in remaining)
        cycle=chain[seen[current]:]+[current]
    return {'modules': len(modules), 'missing_count': len(missing), 'missing': missing[:100],
            'acyclic': not remaining, 'cycle_sample': cycle[:30]}


def finish_report(results, run_tag):
    summary = {'base': BASE, 'run': run_tag, 'results': results,
               'validation': 'Git replay, diff checks and protected-file checks only; no Lean builds.'}
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / 'summary.json').write_text(json.dumps(summary, indent=2))
    index = ROOT / 'report.index'
    old = ENV.get('GIT_INDEX_FILE')
    ENV['GIT_INDEX_FILE'] = str(index)
    try:
        git('read-tree', BASE)
        for path in sorted(OUT.glob('*.json')):
            sha = value('hash-object', '-w', str(path))
            git('update-index', '--add', '--cacheinfo', '100644', sha,
                'verification/rebase-maintenance/' + TAG + '/' + path.name)
        tree = value('write-tree')
        commit = value('commit-tree', tree, '-p', BASE, '-m',
                       'Record systematic open-PR rebase results against ' + TAG)
        branch = 'maintenance/rebase-report-' + TAG + '-' + run_tag
        publish_ref(commit, branch)
        print('REPORT ' + branch, flush=True)
    finally:
        if old is None:
            ENV.pop('GIT_INDEX_FILE', None)
        else:
            ENV['GIT_INDEX_FILE'] = old


def main():
    global BASE, TAG
    if os.environ.get('PR_BATCH') in SNAPSHOT.get('skip_batches', []):
        print('Batch already completed in the first pass', flush=True)
        return
    ROOT.mkdir(parents=True, exist_ok=True)
    OUT.mkdir(parents=True, exist_ok=True)
    run_tag = os.environ.get('GITHUB_RUN_ID', str(int(time.time()))) + '-' + os.environ.get('PR_BATCH', 'all')
    if not REPO.exists():
        subprocess.run(['git', 'init', '--quiet', str(REPO)], check=True)
    git('config', 'user.name', 'github-actions[bot]')
    git('config', 'user.email', '41898282+github-actions[bot]@users.noreply.github.com')
    git('config', 'gc.auto', '0')
    git('config', 'core.quotePath', 'false')
    git('config', 'rerere.enabled', 'false')
    print('FETCH current main', flush=True)
    git('fetch', '--no-tags', UPSTREAM,
        'refs/heads/main:refs/remotes/upstream/main', timeout=1800)
    actual_base = value('rev-parse', 'refs/remotes/upstream/main')
    if actual_base != BASE:
        print('Using current main at run start: ' + actual_base, flush=True)
        BASE = actual_base
        TAG = BASE[:10]
    batches = {
        'owned': [74,80,81,91,97],
        'small-one': [33,54,69,71,75,76,78,82,83],
        'small-two': [62,84,85,86,87,88,90,92,94,95],
        'imports': [4,9,10],
        'imports-4': [4],
        'imports-9': [9],
        'imports-10': [10],
        'pruning': [55,58,61,67],
        'structural': [44,63],
        'performance': [79,98,104],
        'reviewed': [71,74,82,90,92],
        'manual': [94,95],
        'remaining': [33,54,75,88,91,94,95,98],
        'pruning-replay': [55,58,61,67],
    }
    selected = set(batches.get(os.environ.get('PR_BATCH'), [p['n'] for p in SNAPSHOT['prs']]))
    if 'only' in SNAPSHOT:
        selected &= set(SNAPSHOT['only'])
    prs = sorted([p for p in SNAPSHOT['prs'] if p['n'] in selected], key=lambda p: (p['files'] > 1000, p['files'], p['n']))
    print('BASE ' + BASE + ' PRS ' + ','.join(str(p['n']) for p in prs), flush=True)
    specs = ['refs/pull/' + str(p['n']) + '/head:refs/remotes/pr/' + str(p['n']) for p in prs]
    print('FETCH selected PR histories', flush=True)
    git('fetch', '--no-tags', UPSTREAM, *specs, timeout=1800)
    reviewed_config = HERE / 'reviewed-ports.json'
    if reviewed_config.exists():
        reviewed = json.loads(reviewed_config.read_text())
        git('fetch', '--no-tags', OWN, reviewed['reference'] + ':refs/remotes/reviewed/reference')
    print('FETCH complete', flush=True)
    results = []
    for pr in prs:
        number = pr['n']
        result = {'number': number, 'title': pr['title'], 'original_head': pr['head'],
                  'original_repo': pr['repo'], 'original_branch': pr['branch'],
                  'maintainer_can_modify': pr['can_modify']}
        print('::group::PR #' + str(number) + ' ' + pr['title'], flush=True)
        try:
            actual = value('rev-parse', 'refs/remotes/pr/' + str(number))
            if actual != pr['head']:
                result.update(status='branch-advanced', observed_head=actual)
            elif number == 85:
                result['status'] = 'excluded-nonmerging-formatter-pilot'
            else:
                ancestor = value('merge-base', BASE, actual)
                result['old_merge_base'] = ancestor
                if ancestor == actual:
                    result['status'] = 'already-incorporated'
                else:
                    git('rebase', '--abort', check=False)
                    git('checkout', '--detach', '--force', actual, timeout=1800)
                    replay = git('rebase', '--no-update-refs', '--empty=drop', BASE,
                                 timeout=1800, check=False)
                    resolutions = []
                    for _ in range(500):
                        if not replay.returncode:
                            break
                        changes = resolve_manual_ports(number)
                        changes += resolve_deprecated_identifiers(number)
                        changes += resolve_reviewed_ports(number)
                        changes += resolve_module_conflicts(number)
                        resolutions.extend(changes)
                        if not changes or git('ls-files', '-u').stdout:
                            break
                        replay = git('rebase', '--continue', check=False, timeout=1800)
                    result['automatic_resolution_count'] = len(resolutions)
                    result['automatic_resolutions'] = resolutions[:50]
                    if replay.returncode:
                        result.update(status='conflict', **conflict_details())
                        result['rebase_head'] = git('rev-parse', 'REBASE_HEAD', check=False).stdout.strip()
                        result['log_tail'] = (replay.stdout + replay.stderr)[-12000:]
                        checkpoint = value('rev-parse', 'HEAD')
                        result['checkpoint_head'] = checkpoint
                        if checkpoint != BASE:
                            branch = 'maintenance/checkpoint-pr-' + str(number) + '-' + TAG + '-' + run_tag
                            publish_ref(checkpoint, branch)
                            result['checkpoint_branch'] = branch
                        git('rebase', '--abort')
                    else:
                        new = value('rev-parse', 'HEAD')
                        result['rebased_head'] = new
                        diff = git('diff', '--check', BASE, new, check=False)
                        result['diff_check'] = diff.returncode == 0
                        result['diff_check_output'] = diff.stdout[-4000:]
                        result['protected_files'] = {}
                        for path in ['lean-toolchain', 'lake-manifest.json', 'src/Challenge.lean']:
                            before = git('show', BASE + ':' + path, check=False)
                            after = git('show', new + ':' + path, check=False)
                            result['protected_files'][path] = (before.returncode == after.returncode
                                                             and before.stdout == after.stdout)
                        result['changes'] = value('diff', '--shortstat', BASE, new)
                        result['imports'] = import_check()
                        branch = 'maintenance/rebased-pr-' + str(number) + '-' + TAG + '-' + run_tag
                        publish_ref(new, branch)
                        result['prepared_branch'] = branch
                        result['status'] = 'empty-after-rebase' if not result['changes'] else 'rebased'
                        print('PREPARED #' + str(number) + ' ' + new + ' ' + branch, flush=True)
        except Exception as error:
            result.update(status='error', error=str(error)[-5000:])
            git('rebase', '--abort', check=False)
        results.append(result)
        (OUT / ('pr-' + str(number) + '.json')).write_text(json.dumps(result, indent=2))
        print('RESULT ' + json.dumps({k: v for k, v in result.items() if k not in
              ['conflicts', 'log_tail', 'diff_check_output']}), flush=True)
        print('::endgroup::', flush=True)
    finish_report(results, run_tag)
    print('COUNTS ' + json.dumps(dict(collections.Counter(r['status'] for r in results))), flush=True)


if __name__ == '__main__':
    main()
