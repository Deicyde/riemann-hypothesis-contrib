module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRegularity
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps

@[expose] public section


theorem _root_.GlobalTheory.T.kernel_regularity : PositivityTheory.RgBcC.Fc.KerCore := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.kerCore | exact GlobalTheory.CompanionTheory.KerFc.kerCore | (intros; apply GlobalTheory.CompanionTheory.KerFc.kerCore <;> assumption)
