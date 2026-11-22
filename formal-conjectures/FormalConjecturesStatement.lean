/-
Copyright 2025 The Formal Conjectures Authors.
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

The declarations in this file are copied from two files of formal-conjectures, named below.
One thing is changed: the instance is given a name.
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Data.Complex.Basic

/-!
# Declarations copied from formal-conjectures

This file is not part of the submission, and it imports nothing of the submission. It copies,
from [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at commit
`d8d031d4998c78575159ccab9a7a9e95ce043883`, the declarations that the statement of
`GRH.generalized_riemann_hypothesis` depends on and that Mathlib does not have.

They are the work of the formal-conjectures authors, under the license above. Salvatore Mercuri
wrote `GRH.trivialZeros`, the theorem `GRH.generalized_riemann_hypothesis` and the instance in
November 2025, in formal-conjectures pull requests
[1176](https://github.com/google-deepmind/formal-conjectures/pull/1176) and
[1184](https://github.com/google-deepmind/formal-conjectures/pull/1184), and mirefek corrected the
docstring of `trivialZeros` in
[1677](https://github.com/google-deepmind/formal-conjectures/pull/1677).
`verification/NOTES.md` has the rest of the history.

Comparator requires the solution to define every such constant exactly as the challenge does,
and the challenge is formal-conjectures' own file. So nobody has to trust that this copy is
faithful: a copy that differs is rejected.

Like the files it copies from, this file uses Lean's module system. That matters for the proof
`by rfl` below: in a `module` it becomes the constant
`instDecidablePredOddOfDecidableEq_formalConjecturesForMathlib._proof_1` with the statement
`ψ (-1) = -1 ↔ ψ.Odd`, as in formal-conjectures. In a file that is not a `module`, Lean gives
that constant the statement `ψ (-1) = -1 ↔ ψ (-1) = -1`, and Comparator rejects it.
-/

@[expose] public section

namespace DirichletCharacter

/-- From `FormalConjecturesForMathlib/NumberTheory/DirichletCharacter/Basic.lean`. The instance
has no name there. This is the name Lean generates for it in that file, written out because
Comparator matches constants by name. -/
instance instDecidablePredOddOfDecidableEq_formalConjecturesForMathlib
    {S : Type*} [DecidableEq S] [CommRing S] {m : ℕ} :
    DecidablePred (Odd (S := S) (m := m)) :=
  fun ψ ↦ decidable_of_iff (ψ (-1) = -1) <| by rfl

end DirichletCharacter

namespace GRH

/-- From `FormalConjectures/Millennium/RiemannHypothesis.lean`. Its docstring there:

Let $\chi$ be a Dirichlet character, `trivialZeros` is the set of trivial zeros of the
Dirichlet $L$-function of $\chi$ which is always a set of non-positive integers.
- $\chi = 1$ then the Dirichlet $L$-function is the Riemann zeta function, having trivial
  zeroes at all negative even integers (exclude $0$).
- $\chi$ is odd, then the trivial zeroes are the negative odd integers.
- $\chi \neq 1$ is even, then the trivial zeroes are the non-positive even integers. -/
def trivialZeros {q : ℕ} (χ : DirichletCharacter ℂ q) : Set ℤ :=
  if q = 1 then {-2 * (n + 1) | (n : ℕ) } else
    if χ.Odd then { -2 * n - 1 | (n : ℕ) } else
      { - 2 * n | (n : ℕ) }

end GRH
