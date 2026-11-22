# riemann-hypothesis

[![checks](https://github.com/leanprover-community/riemann-hypothesis/actions/workflows/checks.yml/badge.svg)](https://github.com/leanprover-community/riemann-hypothesis/actions/workflows/checks.yml)

A [Comparator](https://github.com/leanprover/comparator) setup and community build cache for the Lean formalization that
claims a proof of the Riemann Hypothesis, and of GRH for Dirichlet L-functions, announced on
2026-11-20 at <https://alpo.ge/remark.pdf>.

The first commit, `40e56bab`, is the submitted Lean source exactly as published. Merged pull
requests have since made the source smaller, mainly by deleting files the proof does not use and
by shortening proofs. `git diff --stat 40e56bab HEAD -- src` shows every change so far, and the
[notes](verification/NOTES.md#source) have more detail. For the original, check out `40e56bab` or
use [riemann-hypothesis-original](https://github.com/homeowmorphism/riemann-hypothesis-original),
which keeps the published source frozen.

This repository also adds Comparator files and cache infrastructure:

| File | What it is |
|---|---|
| [`comparator/Challenge.lean`](comparator/Challenge.lean) | the five theorems, stated in a file that imports only Mathlib |
| [`comparator/main.json`](comparator/main.json) | the Comparator config |
| [`comparator/main-export-targets.txt`](comparator/main-export-targets.txt) | the declarations to export |
| [`comparator/formal-conjectures.json`](comparator/formal-conjectures.json) | a [second Comparator setup](#checking-it-against-formal-conjectures), whose challenge is formal-conjectures' own statement of RH and GRH |
| [`verification/`](verification/NOTES.md) | our notes, and the results once there are some |
| [`scripts/`](scripts/) | public Lake cache configuration and reproducible bootstrap/publishing tools |

## Using the build cache

Fetch and restore Mathlib and this project's compiled modules:

```bash
lake exe cache get
lake build --no-build
```

The cache settings are in `lakefile.toml`; no user configuration is needed. The first command
fetches both caches anonymously and extracts the oleans to `.lake/build`. It prefers a successful
CI build matching the current clean source, configuration, dependency manifest and toolchain;
documentation-only commits can reuse the same cache. Otherwise it tries the original published
cache. The second command checks the default build targets without compiling them. The original
project cache is 4.94 GB and contains portable Lean outputs and generated C. Subsequent ordinary
builds compile changed modules and their dependents.

The community cache includes outputs from **untrusted pull requests and volunteer machines**.
Download integrity checks do not verify proofs. Use an independent fresh build when you need
to trust the result.

The [cache notes](verification/CACHE.md) describe the pinned published archive, the cheaper
bootstrap that reuses its proofs, and how to produce and publish future caches. For independent
verification, follow the clean-build instructions below.

## What is claimed

| Theorem in `Main.lean` | Statement |
|---|---|
| `riemannHypothesis` | Mathlib's `RiemannHypothesis` |
| `riemannZeta_eq_zero_re` | the same, written out |
| `LFunction_ne_zero_of_half_lt_re` | L(χ, s) ≠ 0 for Re s > 1/2, for every modulus and every Dirichlet character, except the trivial character at s = 1 |
| `LFunction_eq_zero_re` | every zero of L(χ, s) with 0 < Re s < 1 has Re s = 1/2 |
| `LFunction_eq_zero_re_of_isPrimitive` | the same, for primitive characters |

## Checking it

```bash
export LEAN_ABORT_ON_PANIC=1   # as Comparator sets it: stop on an internal error, don't continue
export LAKE_ARTIFACT_CACHE=false   # rebuild the submission even if cache-env.sh was sourced earlier
export MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4   # Mathlib's current cache server

# 1. Export the challenge. Clean clone at $CLEAN, Lean v4.36.0.
cd "$CLEAN"
lake exe mathlib/cache get
mkdir -p .lake/comparator
lake env lean --root=comparator -o .lake/comparator/Challenge.olean comparator/Challenge.lean
LEAN_PATH="$PWD/.lake/comparator" lake env leanexport Challenge -- \
  $(cat comparator/main-export-targets.txt) > challenge.export

# 2. Build the solution. Second clone, inside a sandbox with no network. Takes hours.
lake exe mathlib/cache get      # before entering the sandbox
lake build Main         # inside the sandbox

# 3. Export the solution. Still inside the sandbox; only solution.export comes out.
lake env leanexport Main -- $(cat "$CLEAN/comparator/main-export-targets.txt") > solution.export

# 4. Judge. From an empty directory, with the config from the clean clone.
lake comparator --config "$CLEAN/comparator/main.json" \
  --challenge-from-export "$CLEAN/challenge.export" --solution-from-export solution.export
```

What to know before running it:

- **One Lean version.** Since [#66](https://github.com/leanprover-community/riemann-hypothesis/pull/66)
  the project is pinned to Lean `v4.36.0`, which has `lake comparator` and the exporter
  `leanexport` built in. Before that it was on `v4.33.1`, which has neither. The runs the notes
  report were built and exported with `v4.33.1` and the separate lean4export `v4.33.0`, and
  judged with `v4.36.0`.
- **Challenge first.** Compiling the submission runs its code, so the challenge is exported
  where none of that code has been compiled. With Lean and Mathlib `v4.36.0` the export has
  sha256 `ccaa35047adcb2b493ad0ca36abfdd02633b56f5afad009d027b4570ee0f2194`. On the earlier
  pins, Lean `v4.33.1` and Mathlib `0df444a3`, it was
  `bd484ac9886a96f26b1d9a7a59ebd45b7a70d102c015d4f31f9302bbdd6ab2b9`.
- **Frozen challenge.** A pull request may not change a challenge file, a config or a list of
  export targets in `comparator/`: CI fails one that does. So CI does not rebuild the challenge.
- **Not `lake exe cache get`.** In this repository that command also downloads prebuilt files
  for the submission itself, and `lake build Main` then compiles nothing. Steps 1 and 2 use
  `lake exe mathlib/cache get`, which fetches Mathlib only.
- **Cost.** Hours on a large machine, about 100 GB of disk, and a lot of memory for step 4.
- **Moved files.** Until [#88](https://github.com/leanprover-community/riemann-hypothesis/pull/88)
  the three files of this setup were `src/Challenge.lean`, a library in `lakefile.toml`, and
  `comparator.json` and `export-targets.txt` at the root. Their contents are unchanged, and so
  is the challenge export. `lakefile.toml` now describes only the submission and the cache.

The [notes](verification/NOTES.md) have the details: where the source came from, the Lean
version and its known kernel fixes, the tools, the sandboxes, the test of these steps, and the
limits of what a passing run shows.

## Checking it against formal-conjectures

[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) states the Riemann
Hypothesis and the Generalized Riemann Hypothesis in
[`FormalConjectures/Millennium/RiemannHypothesis.lean`](https://github.com/google-deepmind/formal-conjectures/blob/d8d031d4998c78575159ccab9a7a9e95ce043883/FormalConjectures/Millennium/RiemannHypothesis.lean).
Salvatore Mercuri wrote its statement of GRH in November 2025, a year before the announcement,
and the text has not changed since 2025-11-07. It covers every non-trivial zero in the plane,
not only the critical strip. A second setup, in [`comparator/`](comparator/), judges the proof
against those statements, which were written by neither the author nor us:

| File | What it is |
|---|---|
| [`FormalConjecturesChallenge.lean`](comparator/FormalConjecturesChallenge.lean) | the two theorems and what they depend on, copied from formal-conjectures into a file that imports only Mathlib |
| [`formal-conjectures.json`](comparator/formal-conjectures.json) | the Comparator config, for `RiemannHypothesis.riemannHypothesis` and `GRH.generalized_riemann_hypothesis` |
| [`formal-conjectures-export-targets.txt`](comparator/formal-conjectures-export-targets.txt) | the declarations to export |
| [`FormalConjecturesStatement.lean`](comparator/FormalConjecturesStatement.lean) | the two definitions in the GRH statement that Mathlib does not have, for the solution side |
| [`FormalConjecturesBridge.lean`](comparator/FormalConjecturesBridge.lean) | states that GRH and proves `PrimitiveDirichletLZerosOnLine` equivalent to it, from Mathlib and `Statements.lean` alone |
| [`FormalConjecturesSolution.lean`](comparator/FormalConjecturesSolution.lean) | the two theorems under formal-conjectures' names, proved from `Main.lean` |

It adds three steps to the ones above, with the same environment variables:

```bash
# 1b. Export the second challenge. In the clean clone, after step 1.
lake env lean --root=comparator \
  -o .lake/comparator/FormalConjecturesChallenge.olean comparator/FormalConjecturesChallenge.lean
LEAN_PATH="$PWD/.lake/comparator" lake env leanexport FormalConjecturesChallenge -- \
  $(cat comparator/formal-conjectures-export-targets.txt) > fc-challenge.export

# 3b. Compile the three files on the finished build of step 2 and export. Inside the sandbox.
mkdir -p .lake/comparator
for m in FormalConjecturesStatement FormalConjecturesBridge FormalConjecturesSolution; do
  LEAN_PATH="$PWD/.lake/comparator" lake env lean --root=comparator \
    -o ".lake/comparator/$m.olean" "comparator/$m.lean"
done
LEAN_PATH="$PWD/.lake/comparator" lake env leanexport FormalConjecturesSolution -- \
  $(cat "$CLEAN/comparator/formal-conjectures-export-targets.txt") > fc-solution.export

# 4b. Judge, as in step 4.
lake comparator --config "$CLEAN/comparator/formal-conjectures.json" \
  --challenge-from-export "$CLEAN/fc-challenge.export" --solution-from-export fc-solution.export
```

- **A copy, tied to the original.** Comparator needs the challenge and the solution built against
  the same Mathlib, and formal-conjectures follows its own: it is on Lean `v4.33.1`, this project
  on `v4.36.0`. So the challenge is a copy that imports only Mathlib, at formal-conjectures
  commit `d8d031d4998c78575159ccab9a7a9e95ce043883`. It differs from the original in three
  declared ways, and CI compares it with the original's text. Built on formal-conjectures' own
  pins, Comparator finds its statements identical to those formal-conjectures exports.
  The sha256 of `fc-challenge.export` is
  `0977ecc3ea2a1abd7b9b3356a4643574dd65c3b4c8a98ca25b18f5629efe0218`.
- **The solution has its own copy of two definitions.** It cannot import the challenge, which
  declares the theorems it has to prove. `FormalConjecturesStatement.lean` repeats
  `GRH.trivialZeros` and a `Decidable` instance, and `FormalConjecturesBridge.lean` repeats the
  GRH statement. Neither imports the submission's proofs, so nothing there can change how Lean
  reads them. Comparator rejects a copy that differs from the challenge.
- **No Lake library.** Like `Challenge.lean`, these files are in no library of `lakefile.toml`,
  which describes only the submission and the cache. They are compiled directly.
- **Cost.** Step 3b takes minutes, but `fc-solution.export` contains the whole proof again, so
  exporting and judging it cost what steps 3 and 4 do.

The [notes](verification/NOTES.md#formal-conjectures) credit the formal-conjectures authors
whose statements these are, say what was copied and why, and report the runs of these steps: a
rehearsal with a placeholder in place of `Main.lean`, which CI repeats, and an independent run
against a real build on the earlier pins.

## License

The submission belongs to its author and was published without a license. It is mirrored here
for verification only: unmodified at commit `40e56bab`, and changed since then as the
[notes](verification/NOTES.md#source) describe.

The declarations in
[`FormalConjecturesChallenge.lean`](comparator/FormalConjecturesChallenge.lean) and
[`FormalConjecturesStatement.lean`](comparator/FormalConjecturesStatement.lean), and the GRH
statement in [`FormalConjecturesBridge.lean`](comparator/FormalConjecturesBridge.lean), are
copied from [formal-conjectures](https://github.com/google-deepmind/formal-conjectures),
copyright The Formal Conjectures Authors, under the
[Apache License 2.0](https://www.apache.org/licenses/LICENSE-2.0).
