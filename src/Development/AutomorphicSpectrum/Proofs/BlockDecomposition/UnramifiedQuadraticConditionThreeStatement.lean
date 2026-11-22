module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionThree
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.QuadAtOf

@[expose] public section


theorem _root_.GlobalTheory.T.unramified_quadratic_condition_three : PositivityTheory.SiegelWeilFormula.Gunr.Q3 := by
  first | exact @GlobalTheory.CompanionTheory.GunrResCard.q3 | exact GlobalTheory.CompanionTheory.GunrResCard.q3 | (intros; apply GlobalTheory.CompanionTheory.GunrResCard.q3 <;> assumption)
