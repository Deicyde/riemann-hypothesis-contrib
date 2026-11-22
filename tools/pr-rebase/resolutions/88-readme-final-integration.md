# riemann-hypothesis

[![checks](https://github.com/leanprover-community/riemann-hypothesis/actions/workflows/checks.yml/badge.svg)](https://github.com/leanprover-community/riemann-hypothesis/actions/workflows/checks.yml)

A Lean formalization of the Riemann Hypothesis, and of GRH for Dirichlet L-functions.

Levent Alpöge announced it on 2026-11-20 ([remark.pdf](https://alpo.ge/remark.pdf)), and the
first commit, `40e56bab`, is the source as posted. Since then pull requests have deleted files
the proof doesn't use, shortened proofs, and ported it from Lean 4.33.1 to newer releases. The
five theorems in `src/Main.lean`, and the definitions in `src/Statements.lean` that they are
stated with, read exactly as published. `git diff --stat 40e56bab HEAD -- src` lists what has
changed, and
[riemann-hypothesis-original](https://github.com/homeowmorphism/riemann-hypothesis-original)
keeps the original frozen.

**Verification scope:** The cache provides precompiled files for browsing and reuse. The
`checks` workflow checks the challenge statements and comparator configuration; a separate workflow builds pull requests.
A successful cache download or build does not establish that the proof has passed independent
checking. Follow [Checking the proof](#checking-the-proof) for the verification procedure, and
consult the [verification notes](verification/NOTES.md) for recorded results and the source
revisions they cover.

## What is claimed

`src/Main.lean` proves five theorems:

| Theorem | Statement |
|---|---|
| `riemannHypothesis` | Mathlib's `RiemannHypothesis` |
| `riemannZeta_eq_zero_re` | the same, written out |
| `LFunction_ne_zero_of_half_lt_re` | L(χ, s) ≠ 0 for Re s > 1/2, for every modulus and every Dirichlet character, except the trivial character at s = 1 |
| `LFunction_eq_zero_re` | every zero of L(χ, s) with 0 < Re s < 1 has Re s = 1/2 |
| `LFunction_eq_zero_re_of_isPrimitive` | the same, for primitive characters |

[`comparator/Challenge.lean`](comparator/Challenge.lean) states the same five with `sorry` in place of the
proofs, in a file that imports only Mathlib. Comparator checks that `Main.lean` proves exactly
those statements, that it uses no axioms other than `propext`, `Quot.sound` and
`Classical.choice`, and that Lean's kernel and nanoda both accept the proof.

## Getting a build

Compiling the project takes hours on a large machine, so there is a cache of compiled files:

```bash
lake exe cache get
lake build --no-build
```

The first command needs Python 3.11 or newer. It downloads Mathlib's cache and then ours. Ours
has to match your checkout exactly. It looks for a successful CI build of the same source
(commits that only change documentation share one) and, failing that, for the baseline build
pinned in [`scripts/cache-baselines.json`](scripts/cache-baselines.json). If nothing matches,
it says so and you are left with `lake build`. The second command confirms that there is
nothing left to compile.

Don't treat the cache as a check of the proof. It contains files built from unreviewed pull
requests on volunteers' machines, and all the download verifies is that you received what was
uploaded. To check the proof, run Comparator as described below.
[CACHE.md](verification/CACHE.md) explains how the cache is made.

## Checking the proof

```bash
export LEAN_ABORT_ON_PANIC=1        # stop on an internal error, as Comparator does
export LAKE_ARTIFACT_CACHE=false    # really rebuild, even if cache-env.sh was sourced earlier
export MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4

# 1. Export the challenge, in a clean clone at $CLEAN.
cd "$CLEAN"
lake exe mathlib/cache get
mkdir -p .lake/comparator
lake env lean --root=comparator -o .lake/comparator/Challenge.olean comparator/Challenge.lean
LEAN_PATH="$PWD/.lake/comparator" lake env leanexport Challenge -- \
  $(cat comparator/main-export-targets.txt) > challenge.export

# 2. Build the solution, in a second clone, inside a sandbox with no network. Takes hours.
lake exe mathlib/cache get      # before entering the sandbox
lake build Main                 # inside the sandbox

# 3. Export the solution, still inside the sandbox.
lake env leanexport Main -- $(cat "$CLEAN/comparator/main-export-targets.txt") > solution.export

# 4. Judge, from an empty directory, with the same Lean release.
lake comparator --config "$CLEAN/comparator/main.json" \
  --challenge-from-export "$CLEAN/challenge.export" --solution-from-export solution.export
```

Compiling the submission runs its code. That is why the challenge is exported first, in a clone
where none of the submission has been compiled, and why the build and the second export happen
in a sandbox that only `solution.export` leaves.

Steps 1 and 2 use `lake exe mathlib/cache get` on purpose. Plain `lake exe cache get` would also
download our prebuilt copy of the submission, and `lake build Main` would then compile nothing.

The challenge, its config and its list of export targets are in [`comparator/`](comparator/).
None of them is part of the Lake project, which is why step 1 compiles `Challenge.lean`
directly, and pull requests may not change them. Until
[#88](https://github.com/leanprover-community/riemann-hypothesis/pull/88) they were
`src/Challenge.lean`, `comparator.json` and `export-targets.txt`, with the same contents.

All four steps use the Lean release in `lean-toolchain`, which comes with both `leanexport` and
`lake comparator`. The published source was written for Lean 4.33.1, which has neither, so
checking `40e56bab` itself takes two toolchains.
[An older version of this README](https://github.com/leanprover-community/riemann-hypothesis/blob/7cce738ba719a32964ca3822d0994f4c6952c7ae/README.md#checking-it)
has those steps.

We worked these steps out on the published source and don't have a complete run on the current
source yet. Step 1 has been run on it: with Lean 4.36.0, `challenge.export` has sha256
`ccaa35047adcb2b493ad0ca36abfdd02633b56f5afad009d027b4570ee0f2194`. On the published source the
build took hours on a large machine and about 100 GB of disk, and judging needs a lot of memory.
[NOTES.md](verification/NOTES.md) says where the source came from, how the tools and sandboxes
are set up and what a passing run does and doesn't show, but it still describes the Lean 4.33.1
setup, apart from its section on the formal-conjectures statement.

## The formal-conjectures statement

[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) states the Riemann
Hypothesis and the Generalized Riemann Hypothesis in
[`FormalConjectures/Millennium/RiemannHypothesis.lean`](https://github.com/google-deepmind/formal-conjectures/blob/d8d031d4998c78575159ccab9a7a9e95ce043883/FormalConjectures/Millennium/RiemannHypothesis.lean).
Salvatore Mercuri wrote its statement of GRH in November 2025, a year before the announcement.
It covers every non-trivial zero in the plane, not only the critical strip. A second Comparator
setup checks the proof against those statements, which neither the author nor we wrote.

Its challenge is
[`comparator/FormalConjecturesChallenge.lean`](comparator/FormalConjecturesChallenge.lean), a
copy of the formal-conjectures declarations in a file that imports only Mathlib. It has to be a
copy, because Comparator needs the challenge and the solution built against the same Mathlib,
and formal-conjectures follows its own Lean releases. CI compares the copy with
formal-conjectures' text at the commit linked above. On formal-conjectures' own Lean release,
Comparator finds the copy's statements identical to the ones formal-conjectures exports.

Three more files in `comparator/` connect the proof to that challenge.
`FormalConjecturesBridge.lean` proves that the fifth theorem above, the one about primitive
characters, is equivalent to formal-conjectures' GRH, from Mathlib and `src/Statements.lean`
alone. `FormalConjecturesSolution.lean` then proves the two formal-conjectures theorems from
`Main.lean`. `FormalConjecturesStatement.lean` holds two definitions that both need.

Checking it adds three steps to the ones above:

```bash
# 1b. Export the second challenge, in the clean clone, after step 1.
lake env lean --root=comparator \
  -o .lake/comparator/FormalConjecturesChallenge.olean comparator/FormalConjecturesChallenge.lean
LEAN_PATH="$PWD/.lake/comparator" lake env leanexport FormalConjecturesChallenge -- \
  $(cat comparator/formal-conjectures-export-targets.txt) > fc-challenge.export

# 3b. Compile the three files on the finished build of step 2 and export, inside the sandbox.
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

With Lean 4.36.0, `fc-challenge.export` has sha256
`0977ecc3ea2a1abd7b9b3356a4643574dd65c3b4c8a98ca25b18f5629efe0218`, and CI checks that.
`fc-solution.export` contains the whole proof again, so steps 3b and 4b cost what steps 3 and 4
do.

We have run these steps with a placeholder standing in for `Main.lean`, and CI repeats that.
Before the port, ishaan2006 ran them against a real build of the published source.
[NOTES.md](verification/NOTES.md#formal-conjectures) has the results, says what was copied and
why, and credits the formal-conjectures authors.

## CI

A pull request that changes a challenge, a config or a list of export targets in `comparator/`
fails a check. When the formal-conjectures files or anything they depend on changes, CI compares
that challenge with formal-conjectures' text and rehearses the judge with a placeholder for
`Main.lean`. A full build is too big for GitHub's runners, so pull requests are built on
machines lent by volunteers, and successful builds go into the cache. If you have a Linux
machine with plenty of memory and disk to spare, [CI-RUNNERS.md](verification/CI-RUNNERS.md)
explains how to lend it. The scripts behind all this are in [`scripts/`](scripts/) and
[`tools/ci_native/`](tools/ci_native/README.md).

## License

The submission belongs to its author and was published without a license. It is mirrored here
so that it can be checked. Commit `40e56bab` is the unmodified copy.

The declarations in `comparator/` that are copied from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) are copyright The Formal
Conjectures Authors, under the [Apache License 2.0](https://www.apache.org/licenses/LICENSE-2.0).
The files that hold them carry the notice.
