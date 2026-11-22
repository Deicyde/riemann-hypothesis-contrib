module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv

@[expose] public section

open Complex Metric

noncomputable section

namespace Formalism.ZF

lemma zfo_zero_re_lt {ρ : ℂ} {σ : ℝ} (hσ : 1 < σ) (h : riemannZeta ρ = 0) : ρ.re < σ :=
  lt_of_not_ge fun hc => riemannZeta_ne_zero_of_one_lt_re (hσ.trans_le hc) h

lemma zfo_term_re_nonneg {z ρ : ℂ} (n : ℕ) (h : ρ.re < z.re) :
    0 ≤ ((n : ℂ) / (z - ρ)).re := by
  rw [Complex.div_re]; simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero, Complex.sub_re]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) (by linarith)) (Complex.normSq_nonneg _)

lemma zfo_landau (hLL : LandauLocal) {σ τ M : ℝ} (hσ : 1 < σ) (hM : 1 ≤ M)
    (hdiff : DifferentiableOn ℂ riemannZeta (closedBall ((σ : ℂ) + τ * I) (1 / 2)))
    (hbd : ∀ w ∈ closedBall ((σ : ℂ) + τ * I) (1 / 2),
      ‖riemannZeta w‖ ≤ M * ‖riemannZeta ((σ : ℂ) + τ * I)‖) :
    ∃ S : ℝ, 0 ≤ S ∧
      (-(deriv riemannZeta ((σ : ℂ) + τ * I) / riemannZeta ((σ : ℂ) + τ * I))).re
        ≤ 144 * Real.log M - S ∧
      ∀ β : ℝ, riemannZeta ((β : ℂ) + τ * I) = 0 → σ - β ≤ 1 / 6 → 1 / (σ - β) ≤ S := by
  set s : ℂ := (σ : ℂ) + τ * I
  have hsre : s.re = σ := by simp [s]
  have hs0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by rw [hsre]; exact hσ)
  obtain ⟨Z, m, hZ, hm, -, hbound⟩ := hLL riemannZeta s (1 / 2) M (by norm_num) hM hdiff hs0 hbd
  have hZre : ∀ ρ ∈ Z, ρ.re < s.re := fun ρ hρ => hsre.symm ▸ zfo_zero_re_lt hσ ((hZ ρ).1 hρ).2
  refine ⟨∑ ρ ∈ Z, ((m ρ : ℂ) / (s - ρ)).re,
    Finset.sum_nonneg fun ρ hρ => zfo_term_re_nonneg _ (hZre ρ hρ), ?_, ?_⟩
  · have hw := (abs_le.1 ((Complex.abs_re_le_norm _).trans (hbound s (mem_closedBall_self (by norm_num)) hs0))).1
    rw [Complex.sub_re, Complex.re_sum] at hw
    rw [Complex.neg_re]; linarith
  · intro β hβ hβσ
    set ρ : ℂ := (β : ℂ) + τ * I
    have hβlt : β < σ := by simpa [ρ] using zfo_zero_re_lt hσ hβ
    have hdiff' : s - ρ = ((σ - β : ℝ) : ℂ) := by simp only [s, ρ]; push_cast; ring
    have hρZ : ρ ∈ Z := (hZ ρ).2 ⟨by
      rw [mem_closedBall, dist_eq_norm, ← neg_sub, norm_neg, hdiff', Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]; linarith, hβ⟩
    have hterm : ((m ρ : ℂ) / (s - ρ)).re = (m ρ : ℝ) / (σ - β) := by
      rw [hdiff', ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re]
    calc 1 / (σ - β) ≤ (m ρ : ℝ) / (σ - β) :=
          (div_le_div_iff_of_pos_right (by linarith)).2 (by exact_mod_cast hm ρ hρZ)
      _ = ((m ρ : ℂ) / (s - ρ)).re := hterm.symm
      _ ≤ ∑ ρ' ∈ Z, ((m ρ' : ℂ) / (s - ρ')).re :=
          Finset.single_le_sum (f := fun ρ' => ((m ρ' : ℂ) / (s - ρ')).re)
            (fun ρ' hρ' => zfo_term_re_nonneg _ (hZre ρ' hρ')) hρZ

end Formalism.ZF
