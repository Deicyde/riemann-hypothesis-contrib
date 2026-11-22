module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeCalculusHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

@[expose] public section


theorem _root_.GlobalTheory.T.right_derivative_calculus_holds : PositivityTheory.RgBcC.RCalc := by
  first | exact @GlobalTheory.CompanionTheory.RCalc.rcalc | exact GlobalTheory.CompanionTheory.RCalc.rcalc | (intros; apply GlobalTheory.CompanionTheory.RCalc.rcalc <;> assumption)
