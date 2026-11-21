module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSupportFacts
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_support_facts : PositivityTheory.Rg.BcB.G8.Fin.LocSupp := by
  exact @GlobalTheory.CompanionTheory.TwistOrbit.locSupp
