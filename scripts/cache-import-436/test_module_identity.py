#!/usr/bin/env python3
"""Reproduce the volunteer driver's source-root mismatch on a tiny 4.36 fixture.

No network, Mathlib, or project proof build is required. The expected outcome
is that the two real builds produce different private declaration identities.
"""
import json
import os
from pathlib import Path
import subprocess
import tempfile

RELEASE = 'leanprover/lean4:v4.36.0'


def run(args, root, env):
    p = subprocess.run([str(a) for a in args], cwd=root, env=env,
                       text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if p.returncode:
        raise AssertionError(f'{args}:\n{p.stdout}')
    return p.stdout


def fixture(root):
    (root / 'src').mkdir()
    (root / 'raw').mkdir()
    (root / 'lean-toolchain').write_text(RELEASE + '\n')
    (root / 'lakefile.toml').write_text('''name = "moduleIdentityFixture"
srcDir = "src"
defaultTargets = ["Probe"]
[[lean_lib]]
name = "Probe"
''')
    (root / 'src/Probe.lean').write_text('''module
private def hidden : Nat := 7
public def visible : Nat := hidden
''')
    env = {k: v for k, v in os.environ.items() if not k.startswith(('LAKE_', 'LEAN_'))}
    env.update(ELAN_TOOLCHAIN=RELEASE, LAKE_ARTIFACT_CACHE='false', LEAN_ABORT_ON_PANIC='1')
    run(['lake', 'build'], root, env)
    # This is cbuild.py's real command shape: cwd=repo, input=src/...,
    # with no --root and no Lake --setup. The wrapper forwards these arguments.
    run(['lean', 'src/Probe.lean', '-o', 'raw/Probe.olean', '-i', 'raw/Probe.ilean'], root, env)
    inspector = root / 'Inspect.lean'
    inspector.write_text('''import Lean
open Lean
unsafe def main (args : List String) : IO Unit := do
  for base in args do
    let parts ← readModuleDataParts #[base, base ++ ".server", base ++ ".private"]
    let some (data, _) := parts.back? | throw <| IO.userError "missing private part"
    IO.println (toJson (data.constNames.map Name.toString)).compress
''')
    names = [json.loads(s) for s in run(['lean', '--run', inspector,
             '.lake/build/lib/lean/Probe.olean', 'raw/Probe.olean'], root, env).splitlines()]
    stock, volunteer = names
    assert 'visible' in stock and 'visible' in volunteer
    assert '_private.Probe.0.hidden' in stock, stock
    assert '_private.src.Probe.0.hidden' in volunteer, volunteer
    assert '_private.Probe.0.hidden' not in volunteer
    print('PASS: stock Lake uses _private.Probe.0.hidden; the volunteer command uses _private.src.Probe.0.hidden')


if __name__ == '__main__':
    with tempfile.TemporaryDirectory(prefix='volunteer-module-identity-') as d:
        fixture(Path(d).resolve())
