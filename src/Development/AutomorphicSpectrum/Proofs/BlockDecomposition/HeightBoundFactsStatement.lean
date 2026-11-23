module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundFacts
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.FrameDer

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_bound_facts : PositivityTheory.RgBcC.LfSt.HbFacts := by
  exact @GlobalTheory.CompanionTheory.HbBasis.hbFacts
