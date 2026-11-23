module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionCompact
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_function_compact : PositivityTheory.RgBcC.VC.LgCpt := by
  exact @GlobalTheory.CompanionTheory.LgBound.lgCpt
