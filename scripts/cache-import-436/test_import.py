#!/usr/bin/env python3
"""Small stock 4.36 fixtures; no project proof build or network access."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import argparse

TOOLS = Path(__file__).resolve().parent / 'tools'
BIN = TOOLS / '.lake/build/bin'
RELEASE = 'leanprover/lean4:v4.36.0'


def run(args, cwd, env, success=True):
    p = subprocess.run([str(x) for x in args], cwd=cwd, env=env,
                       text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if (p.returncode == 0) != success:
        raise AssertionError(f'{args}: exit {p.returncode}\n{p.stdout}')
    return p.stdout


def fixture(work):
    root, raw, frozen = (work / name for name in ('project', 'raw', 'frozen'))
    for d in (root, raw, frozen):
        d.mkdir()
    sources = {
        'Probe.Base': 'module\npublic theorem base : True := True.intro\n',
        'Probe.Runtime': 'module\nprivate def hidden (n : Nat) : Nat := n + 3\npublic def value : Nat := hidden 4\n',
        'Probe.Initializer': 'module\npublic initialize counter : IO.Ref Nat ← IO.mkRef 41\npublic def current : IO Nat := counter.get\n',
        'Probe.RuntimeConsumer': 'module\nimport all Probe.Runtime\npublic def downstream : Nat := value + 1\n',
        'Probe.Proof': 'module\npublic import Probe.Base\npublic theorem proof : True := base\n',
        'Probe.LeanRuntime': 'module\npublic import Lean\npublic theorem leanProof : True := True.intro\n',
        'Probe.MetaOnly': 'module\nmeta import Lean\npublic theorem metaProof : True := True.intro\n',
        'Probe.Transitive': 'module\npublic import Probe.LeanRuntime\npublic theorem transProof : True := leanProof\n',
        'Probe.ImportAll': 'module\nimport all Probe.Runtime\ntheorem valueProof : value = 7 := rfl\n',
    }
    (root / 'lean-toolchain').write_text(RELEASE + '\n')
    config = ('name = "splitFixture"\nsrcDir = "src"\nplatformIndependent = true\n'
              'defaultTargets = ["Probe"]\n[[lean_lib]]\nname = "Probe"\n'
              'roots = ' + json.dumps(list(sources)) + '\n[[lean_exe]]\nname = \"probe-use\"\nroot = \"Use\"\n')
    (root / 'lakefile.toml').write_text(config)
    for name, source in sources.items():
        p = root / 'src' / (name.replace('.', '/') + '.lean')
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(source)
    env = {k: v for k, v in os.environ.items() if not k.startswith('LAKE_')}
    env.update(ELAN_TOOLCHAIN=RELEASE, LAKE_ARTIFACT_CACHE='false',
               LAKE_CACHE_DIR=str(work / 'cache'), LEAN_ABORT_ON_PANIC='1')
    run(['lake', 'build'], root, env)
    jobs_file, report = work / 'jobs.jsonl', work / 'report.jsonl'
    run(['lake', 'env', BIN / 'index-split', 'plan', root, raw, jobs_file], root, env)
    jobs = [json.loads(s) for s in jobs_file.read_text().splitlines()]
    assert len(jobs) == len(sources)
    suffixes = ('.olean', '.olean.server', '.olean.private', '.ir.sig', '.ir')
    stock = {}
    for job in jobs:
        base = Path(job['olean']).with_suffix('')
        stock[job['name']] = {
            s: Path(str(base) + s).read_bytes() for s in (*suffixes, '.ilean')}
        stock[job['name']]['.c'] = Path(job['c']).read_bytes()
        stock[job['name']]['trace'] = json.loads(Path(job['trace']).read_text())
        saved = work / 'stock' / job['name'].replace('.', '/')
        saved.parent.mkdir(parents=True, exist_ok=True)
        for suffix in suffixes:
            Path(str(saved) + suffix).write_bytes(stock[job['name']][suffix])
    # Exactly the volunteer driver's command shape: no Lake setup and no -c.
    for job in jobs:
        name = job['name']
        destination = raw / (name.replace('.', '/') + '.olean')
        destination.parent.mkdir(parents=True, exist_ok=True)
        source = 'src/' + name.replace('.', '/') + '.lean'
        run(['lean', source, '-o', destination, '-i', destination.with_suffix('.ilean')], root,
            {**env, 'LEAN_PATH': str(raw)})
    shutil.rmtree(root / '.lake/build')
    classification_only = work / 'classification-only.jsonl'
    run([BIN / 'normalize-split', 'classify', jobs_file, classification_only], root, env)
    assert not (root / '.lake/build').exists()
    run([BIN / 'normalize-split', jobs_file, report], root, env)
    assert report.read_bytes() == classification_only.read_bytes()
    classifications = [json.loads(s) for s in report.read_text().splitlines()]
    runtime = {'Probe.Runtime', 'Probe.Initializer', 'Probe.RuntimeConsumer'}
    assert {j['name'] for j in classifications if j['needsCompile']} == runtime
    for job in jobs:
        base = Path(job['olean']).with_suffix('')
        old = frozen / job['name'].replace('.', '/')
        old.parent.mkdir(parents=True, exist_ok=True)
        for s in suffixes:
            shutil.copyfile(str(base) + s, str(old) + s)
        shutil.copyfile(Path(job['input']).with_suffix('.ilean'), job['ilean'])
        if job['name'] not in runtime:
            assert Path(job['c']).read_bytes() == stock[job['name']]['.c'], job['name']
    # Canonical and src-prefixed private names must fail compatibility checking.
    run([BIN / 'normalize-split', 'compare', 'Probe.Runtime',
         frozen / 'Probe/Runtime', work / 'stock/Probe/Runtime', work / 'bad-comparison'],
        root, env, success=False)
    # C generation requires the already archived OLeans, not C/traces for its
    # project imports. Prepare all setups before any runtime C exists.
    setups = work / 'setups.jsonl'
    runtime_work = work / 'runtime'
    run(['lake', 'env', BIN / 'index-split', 'setups', root, jobs_file, report,
         runtime_work, setups], root, env)
    assert not list((root / '.lake/build').rglob('*.trace'))
    by_name = {j['name']: j for j in jobs}
    requests = [json.loads(s) for s in setups.read_text().splitlines()]
    assert {j['name'] for j in requests} == runtime
    for request in requests:
        job = by_name[request['name']]
        fresh = Path(request['setup']).parent / 'fresh'
        setup = fresh.parent / 'setup.json'
        run(['zstd', '-q', '-d', '-f', request['setup'], '-o', setup], root, env)
        run(['lake', 'env', BIN / 'compile-runtime', job['name'], job['source'],
             setup, fresh.with_suffix('.olean'), fresh.with_suffix('.ilean'),
             fresh.with_suffix('.c')], root, env)
        run([BIN / 'normalize-split', 'compare', job['name'],
             frozen / job['name'].replace('.', '/'), fresh, fresh.parent / 'compare'], root, env)
        shutil.copyfile(fresh.with_suffix('.c'), job['c'])
    indexed = work / 'indexed.jsonl'
    run(['lake', 'env', BIN / 'index-split', 'index-ready', root, jobs_file, report,
         indexed], root, env)
    for job in jobs:
        base = Path(job['olean']).with_suffix('')
        old = frozen / job['name'].replace('.', '/')
        for suffix in suffixes:
            assert Path(str(base) + suffix).read_bytes() == Path(str(old) + suffix).read_bytes(), (job['name'], suffix)
    (root / 'src/Use.lean').write_text('module\nimport Probe.Runtime\nimport Probe.Initializer\nimport Probe.RuntimeConsumer\npublic def main : IO Unit := do\n  IO.println value\n  IO.println (← current)\n  IO.println downstream\n')
    run(['lake', 'build', 'probe-use'], root, env)
    assert run([root / '.lake/build/bin/probe-use'], root, env).strip() == '7\n41\n8'
    run(['lake', '--rehash', '--no-build', 'build'], root, env)
    cached = {**env, 'LAKE_ARTIFACT_CACHE': 'true', 'LAKE_RESTORE_ARTIFACTS': 'true'}
    mapping = work / 'outputs.jsonl'
    run(['lake', '--rehash', 'build', '-o', mapping], root, cached)
    assert len(mapping.read_text().splitlines()) == len(sources) + 1
    shutil.rmtree(root / '.lake/build')
    run(['lake', '--rehash', '--no-build', 'build'], root, cached)
    for job in jobs:
        stem = Path(job['olean']).with_suffix('')
        old = frozen / job['name'].replace('.', '/')
        for suffix in suffixes:
            assert Path(str(stem) + suffix).read_bytes() == Path(str(old) + suffix).read_bytes()
        assert Path(job['c']).is_file()
    # Source and option changes must invalidate reconstructed traces.
    changed = root / 'src/Probe/Base.lean'
    changed.write_text(sources['Probe.Base'] + '\n-- change\n')
    run(['lake', '--rehash', '--no-build', 'build'], root, cached, success=False)
    changed.write_text(sources['Probe.Base'])
    (root / 'lakefile.toml').write_text(config + '\n[leanOptions]\nmaxHeartbeats = 12345\n')
    run(['lake', '--rehash', '--no-build', 'build'], root, cached, success=False)
    print('PASS: archived proofs and private identities preserved; C compatibility attested; native consumer and initializer work; cold cache restoration and invalidation work')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work', type=Path, help='keep a fixture in this new directory for inspection')
    args = parser.parse_args()
    if args.work:
        args.work.mkdir(parents=True, exist_ok=False)
        fixture(args.work.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix='split-import-fixture-') as d:
            fixture(Path(d))
