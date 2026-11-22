module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv

@[expose] public section

open Complex MeasureTheory

noncomputable section

namespace Formalism.ZF

theorem norm_sub_le_of_rectangle_identity (Sz R V0 V1 E a b : ℂ) (hS : Sz = (1 / (2 * Real.pi) : ℂ) * (V0 + E))
    (hrect : a - b + I * V0 - I * V1 = 2 * Real.pi * I * R) :
    2 * Real.pi * ‖Sz - R‖ ≤ ‖E‖ + ‖a‖ + ‖b‖ + ‖V1‖ := by
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have h1 : (2 * Real.pi : ℂ) * (Sz - R) = (V0 - 2 * Real.pi * R) + E := by rw [hS]; field_simp; ring
  have h3 : ‖V0 - 2 * Real.pi * R‖ = ‖a - b - I * V1‖ := by
    have := congrArg norm (show I * (V0 - 2 * Real.pi * R) = -(a - b - I * V1) by linear_combination hrect)
    rwa [norm_mul, Complex.norm_I, one_mul, norm_neg] at this
  have h4 : ‖(2 * Real.pi : ℂ) * (Sz - R)‖ = 2 * Real.pi * ‖Sz - R‖ := by
    rw [norm_mul, show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [← h4, h1]
  have h5 : ‖a - b - I * V1‖ ≤ ‖a‖ + ‖b‖ + ‖V1‖ := by
    calc ‖a - b - I * V1‖ ≤ ‖a - b‖ + ‖I * V1‖ := norm_sub_le _ _
      _ ≤ ‖a‖ + ‖b‖ + ‖V1‖ := by rw [norm_mul, Complex.norm_I, one_mul]; linarith [norm_sub_le a b]
  linarith [norm_add_le (V0 - 2 * Real.pi * R) E]

theorem integral_eq_intervalIntegral_add_compl (f : ℝ → ℂ) (hf : Integrable f) (T : ℝ) (hT : 0 ≤ T) :
    ∫ t, f t = (∫ t in (-T)..T, f t) + ∫ t in (Set.Ioc (-T) T)ᶜ, f t := by
  rw [intervalIntegral.integral_of_le (by linarith), integral_add_compl measurableSet_Ioc hf]

end Formalism.ZF
