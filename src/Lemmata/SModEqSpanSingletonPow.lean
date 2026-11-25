module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.SModEq.Basic
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

theorem SModEq.span_singleton_pow_iff_dvd {O : Type*} [CommRing O] (π a b : O) (n : ℕ) :
    a ≡ b [SMOD (Ideal.span {π} ^ n • ⊤ : Submodule O O)] ↔ π ^ n ∣ a - b := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
