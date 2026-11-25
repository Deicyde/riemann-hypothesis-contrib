module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere

@[expose] public section

open MeasureTheory Metric Set

theorem MeasureTheory.Measure.integral_volumeIoiPow (m : ℕ) (φ : ℝ → ℝ) :
    ∫ r : Ioi (0 : ℝ), φ r ∂(Measure.volumeIoiPow m) = ∫ r in Ioi (0 : ℝ), r ^ m * φ r := by
  rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul
    ((measurable_subtypeVal.pow_const m).ennreal_ofReal) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  rw [integral_subtype_comap measurableSet_Ioi (fun r : ℝ => (ENNReal.ofReal (r ^ m)).toReal • φ r)]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt hr) m)]
