# Lean 4.36 cache bootstrap

The selected route is to reuse PR #66's completed volunteer OLeans and supply
the missing Lake cache metadata and runtime outputs. The full archive has passed
integrity verification. The cache adapter is still under test; a full source
rebuild was stopped and its completed work preserved. No new baseline is published.

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

## Preserve the archive's declaration identities

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

The archive also lacks Lake traces, native output maps and generated C. An initial
prototype tried to generate runtime outputs using stock Lake's private identities,
which did not match the archived identities. That establishes a limitation of that
prototype, not that the OLeans must be rebuilt. The adapter should keep the actual
archived private names and proof values. Runtime code generation must match those
names while providing the initializer names expected by canonical imports.

## Stopped source-build attempt on ffmain

- Checkout: `/home/jack/rh436-cache-import/project`, at the PR head above.
- Controller: `/home/jack/rh436-cache-import/run-native-build.sh`.
- Service: `rh436-cache-native-20261122-v2.service` in jack's user manager, stopped.
- Resources: 48 Lake workers, 48 CPU cores of quota, 160 GiB memory cap.
- Build: stock `run-complete-build.py --release leanprover/lean4:v4.36.0`.
- Isolation: no network; home and runtime credentials hidden; writable dependency
  copies belong only to this task. The pre-existing RH comparator is untouched.
- Outputs: `/home/jack/rh436-cache-import/build-records/`.
- Checkpoint/finalizer: `rh436-cache-finish-20261122-v2.service`, also stopped; durable completed
  LTARs and its status live under `/home/jack/rh436-cache-import/cache-data/`.
- Raw build and native-cache data: dedicated `/tmp/rh436-cache-*` directories on
  ffmain's adequately sized memory filesystem; the root filesystem was too small.

At shutdown, 3,218 root module traces and 3,200 durable LTAR checkpoints were
preserved. This was an incomplete source build; it produced no success receipt.
Its finalizer is disabled so it cannot restart work, delete raw outputs, stage,
publish, or activate a baseline.

## Import work

The volunteer archive is being restored on ffmain in a private user/mount
namespace, under `/home/jack/rh436-cache-import/volunteer-fs`. It has a dedicated
inode allowance because the shared `/tmp` filesystem cannot hold all 1.2 million
files. This does not change the host's shared mount settings.

The importer must demonstrate retained archived proof artifacts, valid runtime
symbols, correct stock Lake input hashes, and a cold restoration that elaborates
no project modules. Successful source compilation alone is not that test.
Publication and baseline activation remain pending those checks. Cache production
does not replace the independent mathematical verification in the main README.
