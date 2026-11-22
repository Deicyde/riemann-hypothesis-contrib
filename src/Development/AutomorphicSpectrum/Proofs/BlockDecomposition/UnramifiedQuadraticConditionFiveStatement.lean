module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionFive
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.QuadAtOf

@[expose] public section


theorem _root_.GlobalTheory.T.unramified_quadratic_condition_five : PositivityTheory.SiegelWeilFormula.Gunr.Q5 := by
  first | exact @GlobalTheory.CompanionTheory.GunrInert.isField_tensor_iff_isField_quot | exact GlobalTheory.CompanionTheory.GunrInert.isField_tensor_iff_isField_quot | (intros; apply GlobalTheory.CompanionTheory.GunrInert.isField_tensor_iff_isField_quot <;> assumption)
