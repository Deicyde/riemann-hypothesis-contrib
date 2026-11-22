module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicIntExistsLevelNotDvdMulLift

@[expose] public section


theorem _root_.GlobalTheory.T.padicInt_exists_level_not_dvd_mul_lift : ∀ (l : ℕ) [Fact l.Prime] (c : ℤ_[l]), c ≠ 0 → ∀ e : ℕ, 0 < e → ∃ N : ℕ, ∀ m : ℤ, PadicInt.toZModPow N c = (m : ZMod (l ^ N)) → ¬ ((l : ℤ) ^ N ∣ e * m) := by
  first | exact @GlobalTheory.padicInt_toZModPow_not_dvd_mul | exact GlobalTheory.padicInt_toZModPow_not_dvd_mul | (intros; apply GlobalTheory.padicInt_toZModPow_not_dvd_mul <;> assumption)
