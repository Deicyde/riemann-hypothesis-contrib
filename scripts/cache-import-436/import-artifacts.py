#!/usr/bin/env python3
"""Checkpoint an artifact-preserving import, stopping on any incompatibility.

Run in an offline sandbox with an exact source checkout and stock dependencies.
Runtime source checks get a nested read-only sandbox. This command never uploads
or activates a cache and never falls back to rebuilding the proof library.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import threading

HERE = Path(__file__).resolve().parent
PARTS = ('.olean', '.olean.server', '.olean.private', '.ir.sig', '.ir')


def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def rows(path):
    return [json.loads(line) for line in path.read_text().splitlines()]


def atomic(path, data):
    temporary = path.with_name(path.name + '.pending')
    with temporary.open('w') as stream:
        json.dump(data, stream, sort_keys=True)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    temporary.replace(path)


def run(args, cwd, log=None, env=None):
    subprocess.run([str(x) for x in args], cwd=cwd, check=True, env=env,
                   stdout=log, stderr=subprocess.STDOUT if log else None)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for option in ('project', 'raw', 'records', 'jobs', 'classifications', 'archive-receipt', 'work'):
        parser.add_argument('--' + option, type=Path, required=True)
    parser.add_argument('--helpers', type=Path, default=HERE / 'tools/.lake/build/bin')
    parser.add_argument('--bwrap', type=Path, required=True)
    parser.add_argument('--runtime-workers', type=int, default=4)
    parser.add_argument('--batch-size', type=int, default=512)
    parser.add_argument('--consume-raw', action='store_true',
                        help='remove verified raw working copies only after checkpointing normalized hashes')
    args = parser.parse_args()
    if args.runtime_workers < 1 or args.batch_size < 1:
        parser.error('workers and batch size must be positive')
    pins = json.loads((HERE / 'release.json').read_text())
    receipt = json.loads(args.archive_receipt.read_text())
    if any(receipt.get(k) != pins[k] for k in ('revision', 'archive_sha256', 'files', 'modules')):
        raise ValueError('archive receipt does not match pinned release')
    if args.raw.resolve() != Path(receipt['extraction']).resolve() / 'lean':
        raise ValueError('raw working copy is not the verified extraction')
    project = args.project.resolve()
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project, text=True).strip()
    if head != pins['revision']:
        raise ValueError('import requires the exact archived source revision')
    run(['git', 'diff', '--quiet', 'HEAD', '--', 'src', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'], project)
    version = subprocess.check_output(['lean', '--version'], text=True)
    if '4.36.0' not in version or '611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9' not in version:
        raise ValueError('import requires the pinned stock compiler')
    soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
    resource.setrlimit(resource.RLIMIT_STACK, (hard, hard))
    jobs = rows(args.jobs)
    by_name = {j['name']: j for j in jobs}
    classes = {j['name']: j['needsCompile'] for j in rows(args.classifications)}
    if len(by_name) != pins['modules'] or len(jobs) != len(by_name) or classes.keys() != by_name.keys():
        raise ValueError('module inventory differs from verified release')
    for j in jobs:
        relative = j['name'].replace('.', '/')
        if '..' in relative or Path(relative).is_absolute():
            raise ValueError('unsafe module path')
        expected = {'input': args.raw / (relative + '.olean'),
                    'olean': project / '.lake/build/lib/lean' / (relative + '.olean'),
                    'ilean': project / '.lake/build/lib/lean' / (relative + '.ilean'),
                    'c': project / '.lake/build/ir' / (relative + '.c')}
        if (any(Path(j[k]) != path for k, path in expected.items()) or
                j['source'] != 'src/' + relative + '.lean' or j['package'] != 'tree'):
            raise ValueError('unexpected planned artifact path')
    args.records.mkdir(parents=True, exist_ok=True)
    args.work.mkdir(parents=True, exist_ok=True)
    state = args.records / 'import-state.json'
    provenance = {'revision': head, 'archive_receipt_sha256': sha(args.archive_receipt),
                  'tools': {name: sha(args.helpers / name) for name in
                            ('normalize-split', 'index-split', 'compile-runtime')},
                  'controller_sha256': sha(Path(__file__)), 'proof_verification': False}
    provenance_path = args.records / 'import-provenance.json'
    if provenance_path.exists() and json.loads(provenance_path.read_text()) != provenance:
        raise ValueError('resume requires the same verified inputs and importer binaries')
    atomic(provenance_path, provenance)

    def status(phase, **kw):
        data = {'revision': head, 'phase': phase, 'published': False,
                'proof_verification': False, **kw}
        atomic(state, data)
        print(json.dumps(data), flush=True)

    journal = args.records / 'normalized.jsonl'
    completed = {}
    if journal.exists():
        for item in rows(journal):
            name = item['name']
            if name in completed or name not in by_name:
                raise ValueError('invalid normalization checkpoint')
            if not all(sha(project / p) == value for p, value in item['files'].items()):
                raise ValueError('normalized checkpoint files changed')
            completed[name] = item
    pending = [j for j in jobs if j['name'] not in completed]
    with journal.open('a') as stream:
        for start in range(0, len(pending), args.batch_size):
            batch = pending[start:start + args.batch_size]
            batch_file = args.records / 'normalizing-jobs.jsonl'
            batch_file.write_text(''.join(json.dumps(j) + '\n' for j in batch))
            for j in batch:
                stem = Path(j['olean']).with_suffix('')
                # Retry only while all original parts are still present.
                raw = Path(j['input']).with_suffix('')
                if not all(Path(str(raw) + s).is_file() for s in (*PARTS, '.ilean')):
                    raise ValueError('raw inputs missing without a completed checkpoint')
                for path in [*(Path(str(stem) + s) for s in (*PARTS, '.ilean')),
                             Path(j['c']), Path(j['trace'])]:
                    path.unlink(missing_ok=True)
            report = args.records / 'normalizing-report.jsonl'
            run([args.helpers / 'normalize-split', batch_file, report], project)
            found = {r['name']: r['needsCompile'] for r in rows(report)}
            if found != {j['name']: classes[j['name']] for j in batch}:
                raise ValueError('runtime classification changed during normalization')
            for j in batch:
                shutil.copyfile(Path(j['input']).with_suffix('.ilean'), j['ilean'])
                stem = Path(j['olean']).with_suffix('')
                paths = [Path(str(stem) + s) for s in (*PARTS, '.ilean')]
                if not classes[j['name']]:
                    paths.append(Path(j['c']))
                item = {'name': j['name'], 'files': {str(p.relative_to(project)): sha(p) for p in paths}}
                stream.write(json.dumps(item, sort_keys=True) + '\n')
                completed[j['name']] = item
            stream.flush()
            os.fsync(stream.fileno())
            if args.consume_raw:
                for j in batch:
                    stem = Path(j['input']).with_suffix('')
                    for suffix in (*PARTS, '.ilean', '.cbuild-input', '.cbuild-source'):
                        Path(str(stem) + suffix).unlink(missing_ok=True)
            status('normalizing', modules=len(completed), total=len(jobs))

    setups = args.records / 'runtime-requests.jsonl'
    status('preparing-runtime-setups', modules=len(completed))
    run(['lake', 'env', args.helpers / 'index-split', 'setups', project, args.jobs,
         args.classifications, args.work, setups], project)
    requests = rows(setups)
    if {r['name'] for r in requests} != {n for n, b in classes.items() if b}:
        raise ValueError('runtime request inventory incomplete')
    runtime_records = args.records / 'runtime'
    runtime_records.mkdir(exist_ok=True)
    lock = threading.Lock()
    stopped = threading.Event()
    finished = 0

    def runtime(request):
        nonlocal finished
        name = request['name']
        j = by_name[name]
        marker = runtime_records / (name.replace('.', '/') + '.json')
        marker.parent.mkdir(parents=True, exist_ok=True)
        packed_setup = Path(request['setup'])
        work = packed_setup.parent
        if marker.exists():
            saved = json.loads(marker.read_text())
            if saved['input'] != request['input'] or saved['c_sha256'] != sha(Path(j['c'])):
                raise ValueError('runtime checkpoint changed')
            shutil.rmtree(work)
        else:
            setup = work / 'setup.json'
            run(['zstd', '-q', '-d', '-f', packed_setup, '-o', setup], project)
            old = Path(j['olean']).with_suffix('')
            fresh = work / 'fresh'
            log_path = marker.with_suffix('.log')
            # Source initializers can write only to their temporary output dir.
            command = [args.bwrap, '--die-with-parent', '--unshare-all', '--ro-bind', '/', '/',
                       '--tmpfs', '/tmp', '--proc', '/proc', '--dev', '/dev',
                       '--bind', work, work, '--chdir', project, '--clearenv',
                       '--setenv', 'HOME', '/tmp', '--setenv', 'PATH', '/opt/lean/bin:/usr/bin:/bin',
                       '--setenv', 'LEAN_SYSROOT', '/opt/lean', '--setenv', 'LANG', 'C.UTF-8',
                       '--setenv', 'LEAN_ABORT_ON_PANIC', '1', args.helpers / 'compile-runtime',
                       name, j['source'], setup, fresh.with_suffix('.olean'),
                       fresh.with_suffix('.ilean'), fresh.with_suffix('.c')]
            with log_path.open('w') as log:
                run(command, project, log=log)
                run([args.helpers / 'normalize-split', 'compare', name, old, fresh, work / 'comparison'],
                    project, log=log)
            if not all(sha(project / p) == value for p, value in completed[name]['files'].items()):
                raise ValueError('archived proof artifacts changed during runtime check')
            c = Path(j['c'])
            c.parent.mkdir(parents=True, exist_ok=True)
            temporary = c.with_name(c.name + '.importing')
            shutil.copyfile(fresh.with_suffix('.c'), temporary)
            temporary.replace(c)
            atomic(marker, {'name': name, 'input': request['input'], 'c_sha256': sha(c),
                            'source_sha256': sha(project / j['source']),
                            'proof_artifacts_reused': True, 'all_split_parts_attested': True})
            shutil.rmtree(work)
        with lock:
            finished += 1
            if not stopped.is_set() and (finished % 32 == 0 or finished == len(requests)):
                status('checking-runtime', checked=finished, total=len(requests))

    status('checking-runtime', checked=0, total=len(requests), workers=args.runtime_workers)
    pool = ThreadPoolExecutor(max_workers=args.runtime_workers)
    futures = [pool.submit(runtime, request) for request in requests]
    try:
        for future in as_completed(futures):
            future.result()
    except Exception as error:
        stopped.set()
        status('runtime-compatibility-failed', checked=finished, total=len(requests), error=str(error))
        raise
    finally:
        pool.shutdown(wait=True, cancel_futures=True)
    status('indexing-complete-artifacts', modules=len(jobs))
    run(['lake', 'env', args.helpers / 'index-split', 'index-ready', project, args.jobs,
         args.classifications, args.records / 'indexed.jsonl'], project)
    run(['lake', '--rehash', '--no-build', 'build'], project)
    status('complete-no-build-validated', modules=len(jobs), runtime_checked=len(requests))


if __name__ == '__main__':
    main()
