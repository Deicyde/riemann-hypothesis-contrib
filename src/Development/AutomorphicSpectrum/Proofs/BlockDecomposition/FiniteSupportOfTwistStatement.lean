module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfTwist
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_support_of_twist : PositivityTheory.Rg.BcB.G8.Fin.SuppFinOf := by
  exact @GlobalTheory.CompanionTheory.SuppFinTw.suppFinOf
