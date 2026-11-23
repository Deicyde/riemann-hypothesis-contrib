module

public import Mathlib

@[expose] public section

open scoped ComplexOrder in
theorem UpperTheory.Reformulated.B.ConjEqNegOfSquare.conj_eq_neg_of_sq :
    ∀ {d : ℕ},
    (0 : ℕ) < d → ∀ {z : ℂ}, z ^ (2 : ℕ) = -(↑d : ℂ) → (starRingEnd ℂ : ℂ → ℂ) z = -z := by
  intro d _ z hz
  have hre : z.re = 0 := Complex.sq_nonpos_iff.mp (by
    rw [hz]
    exact neg_nonpos.mpr (Nat.cast_nonneg d))
  apply Complex.ext <;> simp [hre]
