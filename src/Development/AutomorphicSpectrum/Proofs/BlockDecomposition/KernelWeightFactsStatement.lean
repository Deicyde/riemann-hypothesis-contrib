module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelWeightFacts
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_weight_facts : PositivityTheory.RgBcC.Fc.KerW := by
  exact @GlobalTheory.CompanionTheory.KerWord.kerW
