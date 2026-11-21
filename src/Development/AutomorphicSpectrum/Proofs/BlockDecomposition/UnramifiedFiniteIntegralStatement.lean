module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedFiniteIntegral
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.BasisSet

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_finite_integral : PositivityTheory.SiegelWeilFormula.Gunr.FinInt := by
  exact @GlobalTheory.CompanionTheory.Gunr.finInt
