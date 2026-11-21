module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClassLevelFormula
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_level_formula : PositivityTheory.SiegelWeilFormula.Gunr.ClassLev := by
  exact @GlobalTheory.CompanionTheory.GunrClassLev.classLev
