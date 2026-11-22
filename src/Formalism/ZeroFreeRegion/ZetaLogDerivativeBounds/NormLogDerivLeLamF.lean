module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv

@[expose] public section

open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation

noncomputable section

namespace Formalism.ZF

def lamF (σ : ℝ) : ℝ := ∑' n, ‖term ↗Λ (σ : ℂ) n‖

lemma norm_logDeriv_le_lamF {s : ℂ} (hs : 1 < s.re) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤ lamF s.re := by
  have hsum : Summable fun n => ‖term ↗Λ s n‖ := summable_norm_iff.2 (LSeriesSummable_vonMangoldt hs)
  calc ‖deriv riemannZeta s / riemannZeta s‖ = ‖L ↗Λ s‖ := by
        rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_div, norm_neg]
    _ ≤ ∑' n, ‖term ↗Λ s n‖ := norm_tsum_le_tsum_norm hsum
    _ = lamF s.re := tsum_congr fun n => by simp [norm_term_eq]

lemma term_vonMangoldt_real (σ : ℝ) (n : ℕ) :
    term ↗Λ (σ : ℂ) n = ((‖term ↗Λ (σ : ℂ) n‖ : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have h : term ↗Λ (σ : ℂ) n = ((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
    rw [h, Complex.norm_real, Real.norm_of_nonneg (div_nonneg vonMangoldt_nonneg (by positivity))]

lemma lamF_eq_norm {σ : ℝ} (_hσ : 1 < σ) : lamF σ = ‖L ↗Λ (σ : ℂ)‖ := by
  have h : L ↗Λ (σ : ℂ) = ((lamF σ : ℝ) : ℂ) := by
    rw [LSeries, lamF, Complex.ofReal_tsum]; exact tsum_congr (term_vonMangoldt_real σ)
  have hnn : 0 ≤ lamF σ := tsum_nonneg fun _ => norm_nonneg _
  rw [h, Complex.norm_real, Real.norm_of_nonneg hnn]

lemma lamF_anti {σ τ : ℝ} (hσ : 1 < σ) (h : σ ≤ τ) : lamF τ ≤ lamF σ := by
  have hs : ∀ x : ℝ, 1 < x → Summable fun n => ‖term ↗Λ (x : ℂ) n‖ := fun x hx =>
    summable_norm_iff.2 (LSeriesSummable_vonMangoldt (by simpa using hx))
  refine Summable.tsum_le_tsum (fun n => ?_) (hs τ (by linarith)) (hs σ hσ)
  rw [norm_term_eq, norm_term_eq]
  split_ifs with hn
  · rfl
  · exact div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn) (by simpa using h))

end Formalism.ZF
