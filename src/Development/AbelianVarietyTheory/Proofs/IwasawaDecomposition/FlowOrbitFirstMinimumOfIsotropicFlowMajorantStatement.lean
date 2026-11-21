module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlowOrbitFirstMinimumOfIsotropicFlowMajorant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt

@[expose] public section

open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flowOrbitFirstMinimum_of_isotropicFlowMajorant : FlowMajSt → OrbitThickSt := by
  exact @GlobalTheory.CuspFrom.OrbitThick.orbitThick_of_flowMaj
