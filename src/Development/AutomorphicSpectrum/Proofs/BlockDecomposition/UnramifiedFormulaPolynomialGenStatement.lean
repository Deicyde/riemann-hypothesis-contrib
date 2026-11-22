module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedFormulaPolynomialGen
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf

@[expose] public section


theorem _root_.GlobalTheory.T.unramified_formula_polynomial_gen : PositivityTheory.PfSWUS.Loc.UnrFormula → PositivityTheory.SiegelWeilFormula.Gen.UnrPoly := by
  first | exact @GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries.unrPoly | exact GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries.unrPoly | (intros; apply GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries.unrPoly <;> assumption)
