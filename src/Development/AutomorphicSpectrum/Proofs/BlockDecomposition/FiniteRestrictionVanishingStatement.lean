module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteRestrictionVanishing
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_restriction_vanishing : PositivityTheory.Rg.BcB.G8.Fin.RestrV := by
  exact @GlobalTheory.CompanionTheory.EulerV.main
