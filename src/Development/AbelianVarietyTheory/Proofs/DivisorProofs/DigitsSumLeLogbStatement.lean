module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DigitsSumLeLogb

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.digits_sum_le_mul_logb : ∀ (p n : ℕ), p.Prime → (((Nat.digits p n).sum : ℕ) : ℝ) ≤ ((p : ℝ) - 1) * Real.logb p ((n : ℝ) + 1) := by
  exact @GlobalTheory.digits_sum_le_logb
