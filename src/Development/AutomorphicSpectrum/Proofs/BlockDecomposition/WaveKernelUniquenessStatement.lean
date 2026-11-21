module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniqueness
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wave_kernel_uniqueness : PositivityTheory.RgBcC.KerUniq := by
  exact @GlobalTheory.CompanionTheory.KerUniq.main
