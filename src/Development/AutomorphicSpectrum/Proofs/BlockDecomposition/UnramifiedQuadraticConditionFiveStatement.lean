module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionFive
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.QuadAtOf

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_condition_five : PositivityTheory.SiegelWeilFormula.Gunr.Q5 := by
  exact @GlobalTheory.CompanionTheory.GunrInert.isField_tensor_iff_isField_quot
