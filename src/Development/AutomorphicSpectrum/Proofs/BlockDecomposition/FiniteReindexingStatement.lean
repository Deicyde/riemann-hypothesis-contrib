module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteReindexing
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_reindexing : PositivityTheory.Rg.BcB.G8.Fin.Reindex := by
  exact @GlobalTheory.CompanionTheory.SecReindex.reindex
