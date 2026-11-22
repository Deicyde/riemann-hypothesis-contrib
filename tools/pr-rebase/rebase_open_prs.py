#!/usr/bin/env python3
"""Rebase pinned public RH PRs in isolation, preserving original Git authors.

Only publishes new preparation/checkpoint/report branches in Jack's fork.
Never updates contributors' branches, merges PRs, executes PR code or builds Lean.
Conflicts remain explicit; no blanket ours/theirs conflict policy is used.
"""
import base64
import collections
import json
import os
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
    ROOT.mkdir(parents=True, exist_ok=True)
    OUT.mkdir(parents=True, exist_ok=True)
    run_tag = os.environ.get('GITHUB_RUN_ID', str(int(time.time())))
    if not REPO.exists():
        subprocess.run(['git', 'init', '--quiet', str(REPO)], check=True)
    git('config', 'gc.auto', '0')
    git('config', 'core.quotePath', 'false')
    git('config', 'rerere.enabled', 'false')
    git('fetch', '--no-tags', UPSTREAM,
        'refs/heads/main:refs/remotes/upstream/main', timeout=1800)
    actual_base = value('rev-parse', 'refs/remotes/upstream/main')
    if actual_base != BASE:
        print('Using current main at run start: ' + actual_base, flush=True)
        BASE = actual_base
        TAG = BASE[:10]
    prs = sorted(SNAPSHOT['prs'], key=lambda p: (p['files'] > 1000, p['files'], p['n']))
    specs = ['refs/pull/' + str(p['n']) + '/head:refs/remotes/pr/' + str(p['n']) for p in prs]
    git('fetch', '--no-tags', UPSTREAM, *specs, timeout=1800)
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
                    replay = git('rebase', '--no-update-refs', '--empty=drop', '--onto', BASE,
                                 ancestor, timeout=1800, check=False)
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
