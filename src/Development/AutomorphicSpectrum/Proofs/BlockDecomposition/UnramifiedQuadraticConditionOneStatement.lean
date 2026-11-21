module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.QuadAtOf

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_condition_one : PositivityTheory.SiegelWeilFormula.Gunr.Q1 := by
  exact @GlobalTheory.CompanionTheory.ResidueInvolution.q1
