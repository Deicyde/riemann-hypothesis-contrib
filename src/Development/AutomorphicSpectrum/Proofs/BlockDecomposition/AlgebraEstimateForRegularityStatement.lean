module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraEstimateForRegularity
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebra_estimate_for_regularity : PositivityTheory.RgBcC.AlgEst := by
  exact @GlobalTheory.CompanionTheory.SkewWords.algEst
