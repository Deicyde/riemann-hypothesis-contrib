# Lean 4.36 cache bootstrap

The completed volunteer build for PR #66 is useful build evidence, but is not a
drop-in stock Lake cache. A separate stock default-target build is running on
ffmain to produce the accepted cache map and receipt. The active public baseline
remains unchanged until the new cache has passed publication and cold restoration.

## Verified release

Release: <https://github.com/Vilin97/rh-lc/releases/tag/lean-4.36-build-5a1fb95adc>.

| Input | Identity |
|---|---|
| PR head | `9b1ee6011d0433c4c38a90508a14d39e33d608b6` |
| Source tree | `0ba0b4d44fa26b97a376ec10889be6b553237103` |
| Lean | `v4.36.0`, commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9` |
| Mathlib | `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` |
| Archive SHA256 | `c652456b1f0e35e98b9a0b809f807e729db6cfaad76c986c20fa618f1781d1fb` |
| Checked files | 1,195,160 |
| Modules | 149,395 |
| Total unpacked file bytes | 82,466,169,920 |

The complete archive was streamed and checked on ffmain: every compressed part,
the combined archive, and every extracted file matched the pinned SHA256 values.
Inspection retained no full uncompressed archive. The receipt is
`/home/jack/rh436-cache-import/inspect-20261122/verified-archive.json`.

The release pins and bounded streaming verifier are in
[`scripts/cache-import-436/`](../scripts/cache-import-436/). To repeat verification:

```bash
python3 scripts/cache-import-436/fetch-release.py \
  --inspect --max-unpacked-gib 100 --output /path/to/new/inspection
```

This verifies artifact identity and integrity, not proofs.

## Why package normalization is insufficient

The published `cbuild.py` runs Lean from the repository directory with a source
argument such as `src/CompanionTheory/.../FourLeOfFive.lean`. It supplies neither
`--root=src` nor Lake's `--setup` file. Stock Lean therefore infers the main module
name with a leading `src` component. In contrast, Lake supplies the actual module
name through its setup file.

That changes private declaration names. A real artifact from this release,
`CompanionTheory.AutomorphicTheory.BesselWaveGrids.FourLeOfFive.olean.private`,
contains the private theorem named
`_private.src.CompanionTheory.AutomorphicTheory.BesselWaveGrids.FourLeOfFive.0.CompanionTheory.WaveGrid.exists_ge_four_fifths_pow_qw_eq_mul_of_far_letters`.
Stock Lake's corresponding private prefix omits `src`.

The small reproducible check is:

```bash
python3 scripts/cache-import-436/test_module_identity.py
```

It compiles the same fixture using stock Lake and the volunteer driver's command.
The public declaration keeps its name, while the private definition is respectively
`_private.Probe.0.hidden` and `_private.src.Probe.0.hidden`.

The archive also lacks Lake traces, native output maps and generated C. Simply
normalizing package metadata and recompiling executable modules can therefore
mix incompatible private identities and native symbols. A general converter would
need to account for these identities throughout constants, proofs, compiler data
and environment extensions. The running stock build avoids that transformation.

## Native producer on ffmain

- Checkout: `/home/jack/rh436-cache-import/project`, at the PR head above.
- Controller: `/home/jack/rh436-cache-import/run-native-build.sh`.
- Service: `rh436-cache-native-20261122-v2.service` in jack's user manager.
- Resources: 48 Lake workers, 48 CPU cores of quota, 160 GiB memory cap.
- Build: stock `run-complete-build.py --release leanprover/lean4:v4.36.0`.
- Isolation: no network; home and runtime credentials hidden; writable dependency
  copies belong only to this task. The pre-existing RH comparator is untouched.
- Outputs: `/home/jack/rh436-cache-import/build-records/`.
- Checkpoint/finalizer: `rh436-cache-finish-20261122-v2.service`; durable completed
  LTARs and its status live under `/home/jack/rh436-cache-import/cache-data/`.
- Raw build and native-cache data: dedicated `/tmp/rh436-cache-*` directories on
  ffmain's adequately sized memory filesystem; the root filesystem was too small.

The standard wrapper verifies committed source and locked dependency inputs both
before and after the build. It writes `build-receipt.json` only on successful
completion. No volunteer artifacts are installed into this build.

The finalizer checkpoints completed compressed outputs to disk while the build
runs. On a successful receipt it invokes the standard stager, checks the staged
archives with stock hashes and SHA256, and performs a full cold stock restoration
with `--rehash --no-build`. It revalidates source/dependency identity afterwards.
Only after durable staging may it replace this task's reproducible raw memory-file
outputs to make room for that restoration. A failure stops the pipeline and leaves
its status and durable artifacts available for inspection.

After a passed cold restoration, publish from the credential host, verify the
public map and index, and fill the 4.36 baseline pins in `scripts/cache-baselines.json`.
The finalizer writes `cache-data/ready-baseline.json` and never publishes or
activates it. Cache production does not replace the independent mathematical
verification described in the main README.
