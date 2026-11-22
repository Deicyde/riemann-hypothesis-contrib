module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LdrMid

@[expose] public section

open Complex

noncomputable section

namespace Formalism.ZF

theorem logDerivBoundInRegionOfBounds : LogDerivRegionOf := by
  intro hZF hLR hG hI hSH hLL
  obtain ⟨c₀, hc₀, hZ0⟩ := hZF
  obtain ⟨CR, hCR0, hCR⟩ := hLR
  obtain ⟨cS, CS, hcS, hCS⟩ := hSH (Real.exp 24)
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  set c := min (min (c₀ / 4) 1) (cS * Real.log 2)
  have hcpos : 0 < c := lt_min (lt_min (by linarith) one_pos) (mul_pos hcS (by linarith))
  have hc1 : c ≤ c₀ / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hc2 : c ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hc3 : c ≤ cS * Real.log 2 := min_le_right _ _
  have hK1 : 0 ≤ 1441 + 60 / c₀ := by positivity
  have hK3 : 0 ≤ 4 * |CS| := by positivity
  refine ⟨c, (1441 + 60 / c₀) + (4 + 4 * CR) + 4 * |CS|, hcpos, fun s hs1 hreg => ?_⟩
  set σ := s.re; set t := s.im; set L := Real.log (|t| + 2)
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hL0 : 0 < L := by linarith
  have hLsq : 1 / 4 ≤ L ^ 2 := by nlinarith
  by_cases hright : 1 + 1 / L < σ
  · have hσ1 : 1 < σ := by linarith [show 0 < 1 / L by positivity]
    have hnorm : σ - 1 ≤ ‖s - 1‖ := (le_abs_self _).trans (by simpa [σ] using Complex.abs_re_le_norm (s - 1))
    have hσL : 1 / (σ - 1) ≤ L := (div_le_iff₀ (by linarith)).mpr (by linarith [(div_lt_iff₀ hL0).mp (show 1 / L < σ - 1 by linarith)])
    have h2 : ‖1 / (s - 1)‖ ≤ L := by
      rw [norm_div, norm_one]; exact (one_div_le_one_div_of_le (by linarith) hnorm).trans hσL
    have hsum := (norm_add_le (deriv riemannZeta s / riemannZeta s) (1 / (s - 1))).trans (add_le_add (hCR s hσ1) h2)
    nlinarith [mul_nonneg hCR0 (sq_nonneg L), mul_nonneg hK1 (sq_nonneg L), mul_nonneg hK3 (sq_nonneg L)]
  · by_cases hbig : 24 ≤ L
    · have hm := Formalism.ZF.ldr_mid hZ0 hc₀ hG hI hLL (σ := σ) (t := t) hbig
        (by linarith [show c / L ≤ (c₀ / 4) / L by gcongr])
        (by linarith [show c / L ≤ 1 / L by gcongr]) (le_of_not_gt hright)
      have hs : (σ : ℂ) + t * I = s := Complex.re_add_im s
      rw [hs] at hm
      nlinarith [mul_nonneg hK3 (sq_nonneg L), mul_nonneg hCR0 (sq_nonneg L)]
    · have htT : |t| ≤ Real.exp 24 := by
        linarith [(Real.log_lt_iff_lt_exp (by positivity)).mp (lt_of_not_ge hbig)]
      have hcL : c / L ≤ cS := (div_le_iff₀ hL0).mpr (by nlinarith)
      have hinv : 1 / L ≤ 2 := (div_le_iff₀ hL0).mpr (by linarith)
      have hb := hCS s hs1 htT (by linarith) (by linarith)
      nlinarith [le_abs_self CS, abs_nonneg CS, mul_nonneg hK1 (sq_nonneg L), mul_nonneg hCR0 (sq_nonneg L)]

end Formalism.ZF
