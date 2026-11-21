module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeHomotopy
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_cone_homotopy : PositivityTheory.RgBcC.Homot := by
  exact @GlobalTheory.CompanionTheory.SuperHomot.homot
