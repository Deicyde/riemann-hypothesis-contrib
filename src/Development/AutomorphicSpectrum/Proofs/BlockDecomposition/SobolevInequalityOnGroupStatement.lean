module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevInequalityOnGroup
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_inequality_on_group : PositivityTheory.RgBcC.SobG := by
  exact @GlobalTheory.CompanionTheory.SobGL.sobG
