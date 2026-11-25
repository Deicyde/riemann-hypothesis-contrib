module

public import Mathlib.NumberTheory.ModularForms.Cusps

@[expose] public section

theorem CongruenceSubgroup.one_mem_strictPeriods_map_Gamma1 (N : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
  rw [strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples 1
