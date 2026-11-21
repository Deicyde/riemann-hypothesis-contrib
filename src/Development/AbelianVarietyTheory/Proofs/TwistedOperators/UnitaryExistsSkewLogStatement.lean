module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryExistsSkewLog

@[expose] public section

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_skewHermitian_log_of_unitary : ∀ (n : ℕ) (k : Matrix (Fin n) (Fin n) ℂ), kᴴ * k = 1 → ∃ (X : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ), Xᴴ = -X ∧ NormedSpace.exp X = k ∧ X = Polynomial.aeval k p := by
  exact @GlobalTheory.unitary_exists_skew_log
