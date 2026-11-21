module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureOperatorFacts
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_operator_facts : PositivityTheory.RgBcC.Fc.ClsFacts := by
  exact @GlobalTheory.CompanionTheory.FcCls.clsFacts
