module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv

@[expose] public section

open Complex MeasureTheory

noncomputable section

namespace Formalism.ZF

theorem norm_perronIntegrand (y : ℝ) (hy : 0 < y) (w : ℂ) :
    ‖Fy y w‖ = ‖deriv riemannZeta w / riemannZeta w‖ * y ^ w.re / (‖w‖ * ‖w - 1‖) := by
  simp only [Fy, norm_div, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hy]

theorem one_sub_div_log_le (c c' T v : ℝ) (hc : 0 < c) (hcc : c ≤ c') (_hT : 0 ≤ T) (hv : |v| ≤ T) :
    1 - c' / Real.log (|v| + 2) ≤ 1 - c / Real.log (T + 2) := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : 0 < Real.log (|v| + 2) := h2.trans_le (Real.log_le_log (by norm_num) (by linarith [abs_nonneg v]))
  have hle : Real.log (|v| + 2) ≤ Real.log (T + 2) := Real.log_le_log (by linarith [abs_nonneg v]) (by linarith)
  have e1 := div_le_div_of_nonneg_left hc.le hpos hle
  have e2 := div_le_div_of_nonneg_right hcc hpos.le
  linarith

theorem riemannZeta_ne_zero_of_mem_rectangle (c₀ : ℝ)
    (hZ : ∀ s : ℂ, s ≠ 1 → 1 - c₀ / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0)
    (c T σ₀ : ℝ) (hc : 0 < c) (hcc : c ≤ c₀) (hT : 0 ≤ T) :
    ∀ w : ℂ, 1 - c / Real.log (T + 2) ≤ w.re → w.re ≤ σ₀ → |w.im| ≤ T → w ≠ 1 →
      riemannZeta w ≠ 0 :=
  fun w h1 _ h3 h4 => hZ w h4 ((one_sub_div_log_le c c₀ T w.im hc hcc hT h3).trans h1)

theorem norm_perronIntegrand_le_right (C₂ : ℝ)
    (hR : ∀ s : ℂ, 1 < s.re → ‖deriv riemannZeta s / riemannZeta s‖ ≤ 1 / (s.re - 1) + C₂)
    (y T t : ℝ) (hy : 1 < y) (hT : 0 < T) (ht : T ≤ |t|) :
    ‖Fy y (((1 + 1 / Real.log y : ℝ) : ℂ) + t * I)‖ ≤
      (Real.log y + C₂) * (Real.exp 1 * y) / t ^ 2 := by
  set w : ℂ := ((1 + 1 / Real.log y : ℝ) : ℂ) + t * I
  have hl : 0 < Real.log y := Real.log_pos hy
  have hre : w.re = 1 + 1 / Real.log y := by simp [w]
  have hy0 : 0 < y := by linarith
  rw [norm_perronIntegrand y hy0 w]
  have hζ : ‖deriv riemannZeta w / riemannZeta w‖ ≤ Real.log y + C₂ := by
    simpa [hre] using hR w (by rw [hre]; linarith [one_div_pos.mpr hl])
  have hpow : y ^ w.re = Real.exp 1 * y := by
    rw [hre, Real.rpow_add hy0, Real.rpow_one, Real.rpow_def_of_pos hy0, mul_one_div_cancel hl.ne']; ring
  have hw1 : |t| ≤ ‖w‖ := by simpa [w] using Complex.abs_im_le_norm w
  have hw2 : |t| ≤ ‖w - 1‖ := by simpa [w] using Complex.abs_im_le_norm (w - 1)
  have hden : t ^ 2 ≤ ‖w‖ * ‖w - 1‖ := by rw [← sq_abs]; nlinarith [abs_nonneg t]
  rw [hpow]
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hζ (by positivity)) (by positivity)).trans
    (div_le_div_of_nonneg_left (mul_nonneg ((norm_nonneg _).trans hζ) (by positivity))
      (by rw [← sq_abs]; exact pow_pos (hT.trans_le ht) 2) hden)

theorem norm_perronIntegrand_le_horizontal (c₁ C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hD : ∀ s : ℂ, s ≠ 1 → 1 - c₁ / Real.log (|s.im| + 2) ≤ s.re →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ C₁ * Real.log (|s.im| + 2) ^ 2)
    (c y T x v σ₀ : ℝ) (hc : 0 < c) (hcc : c ≤ c₁) (hy : 1 ≤ y) (hT : 1 ≤ T) (hv : |v| = T)
    (hx1 : 1 - c / Real.log (T + 2) ≤ x) (hx2 : x ≤ σ₀) :
    ‖Fy y ((x : ℂ) + (v : ℂ) * I)‖ ≤
      (C₁ * Real.log (T + 2) ^ 2 + 1) * y ^ σ₀ / T ^ 2 := by
  set w : ℂ := (x : ℂ) + (v : ℂ) * I
  have hre : w.re = x := by simp [w]
  have him : w.im = v := by simp [w]
  rw [norm_perronIntegrand y (by linarith) w]
  have hw1 : T ≤ ‖w‖ := by rw [← hv, ← him]; exact Complex.abs_im_le_norm w
  have hw2 : T ≤ ‖w - 1‖ := by rw [← hv, ← show (w - 1).im = v by simp [him]]; exact Complex.abs_im_le_norm _
  have hne : w ≠ 1 := fun h => by rw [h, sub_self, norm_zero] at hw2; linarith
  have hD' := hD w hne (by rw [hre]; exact (one_sub_div_log_le c c₁ T w.im hc hcc (by linarith) (by rw [him, hv])).trans hx1)
  rw [him, hv] at hD'
  have hinv : ‖1 / (w - 1)‖ ≤ 1 := by rw [norm_div, norm_one]; exact (div_le_one (by linarith)).mpr (by linarith)
  have hζ : ‖deriv riemannZeta w / riemannZeta w‖ ≤ C₁ * Real.log (T + 2) ^ 2 + 1 := by
    have := norm_sub_le (deriv riemannZeta w / riemannZeta w + 1 / (w - 1)) (1 / (w - 1))
    simp only [add_sub_cancel_right] at this; linarith
  have hpow : y ^ w.re ≤ y ^ σ₀ := by rw [hre]; exact Real.rpow_le_rpow_of_exponent_le hy hx2
  calc ‖deriv riemannZeta w / riemannZeta w‖ * y ^ w.re / (‖w‖ * ‖w - 1‖)
      ≤ (C₁ * Real.log (T + 2) ^ 2 + 1) * y ^ σ₀ / (‖w‖ * ‖w - 1‖) := by gcongr
    _ ≤ (C₁ * Real.log (T + 2) ^ 2 + 1) * y ^ σ₀ / T ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)

theorem norm_perronIntegrand_le_left (c₁ C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hD : ∀ s : ℂ, s ≠ 1 → 1 - c₁ / Real.log (|s.im| + 2) ≤ s.re →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ C₁ * Real.log (|s.im| + 2) ^ 2)
    (c y T u : ℝ) (hc : 0 < c) (hcc : c ≤ c₁) (hy : 0 < y) (hT : 0 ≤ T) (hu : |u| ≤ T)
    (hhalf : 1 / 2 ≤ 1 - c / Real.log (T + 2)) :
    ‖Fy y (((1 - c / Real.log (T + 2) : ℝ) : ℂ) + u * I)‖ ≤
      (C₁ * Real.log (T + 2) ^ 2 + Real.log (T + 2) / c) * y ^ (1 - c / Real.log (T + 2)) *
        (2 * Real.log (T + 2) / c) := by
  set L := Real.log (T + 2)
  have hL : 0 < L := Real.log_pos (by linarith)
  set w : ℂ := (((1 - c / L : ℝ)) : ℂ) + u * I
  have hre : w.re = 1 - c / L := by simp [w]
  have him : w.im = u := by simp [w]
  rw [norm_perronIntegrand y hy w]
  have hcL : 0 < c / L := div_pos hc hL
  have hw1 : 1 / 2 ≤ ‖w‖ := by have := Complex.abs_re_le_norm w; rw [hre, abs_of_pos (by linarith)] at this; linarith
  have hw2 : c / L ≤ ‖w - 1‖ := by
    simpa [hre, abs_of_pos hcL] using Complex.abs_re_le_norm (w - 1)
  have hne : w ≠ 1 := fun h => by rw [h, sub_self, norm_zero] at hw2; linarith
  have hD' := hD w hne (by rw [hre, him]; exact one_sub_div_log_le c c₁ T u hc hcc hT hu)
  rw [him] at hD'
  have hlogu : Real.log (|u| + 2) ^ 2 ≤ L ^ 2 :=
    pow_le_pow_left₀ (Real.log_nonneg (by linarith [abs_nonneg u]))
      (Real.log_le_log (by linarith [abs_nonneg u]) (by linarith)) 2
  have hinv : ‖1 / (w - 1)‖ ≤ L / c := by
    rw [norm_div, norm_one, div_le_div_iff₀ (hcL.trans_le hw2) hc]
    have := mul_le_mul_of_nonneg_left hw2 hL.le; rw [mul_div_cancel₀ _ hL.ne'] at this; linarith
  have hζ : ‖deriv riemannZeta w / riemannZeta w‖ ≤ C₁ * L ^ 2 + L / c := by
    have := norm_sub_le (deriv riemannZeta w / riemannZeta w + 1 / (w - 1)) (1 / (w - 1))
    simp only [add_sub_cancel_right] at this
    linarith [hD'.trans (mul_le_mul_of_nonneg_left hlogu hC₁)]
  have hden : c / (2 * L) ≤ ‖w‖ * ‖w - 1‖ := by
    rw [show c / (2 * L) = (1 / 2) * (c / L) by field_simp]
    exact mul_le_mul hw1 hw2 hcL.le (by linarith)
  rw [hre]
  calc ‖deriv riemannZeta w / riemannZeta w‖ * y ^ (1 - c / L) / (‖w‖ * ‖w - 1‖)
      ≤ (C₁ * L ^ 2 + L / c) * y ^ (1 - c / L) / (‖w‖ * ‖w - 1‖) := by gcongr
    _ ≤ (C₁ * L ^ 2 + L / c) * y ^ (1 - c / L) / (c / (2 * L)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = (C₁ * L ^ 2 + L / c) * y ^ (1 - c / L) * (2 * L / c) := by field_simp

end Formalism.ZF
