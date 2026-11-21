module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePropagationSpeedHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_propagation_speed_holds : PositivityTheory.RgBcC.AsmSpeed := by
  exact @GlobalTheory.CompanionTheory.WaveSpd.asmSpeed
