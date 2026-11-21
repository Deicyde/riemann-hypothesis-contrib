module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FriedrichsExtensionFacts
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.friedrichs_extension_facts : PositivityTheory.RgBcC.Fc.Friedrichs := by
  exact @GlobalTheory.CompanionTheory.FriedrichsFc.friedrichs
