module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonInert
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_comparison_inert : PositivityTheory.Rg.BcB.G8.Fin.LocCompareInert := by
  exact @GlobalTheory.CompanionTheory.LocInert.locCompareInert
