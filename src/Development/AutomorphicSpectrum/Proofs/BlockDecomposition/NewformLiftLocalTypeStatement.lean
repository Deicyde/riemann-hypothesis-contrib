module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLocalType
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

@[expose] public section


theorem _root_.GlobalTheory.T.newform_lift_local_type : Ad3.R.B0 → Ad3.R.HeckeSumLocalTranslates := by
  first | exact @GlobalTheory.CompanionTheory.RSq.f3a | exact GlobalTheory.CompanionTheory.RSq.f3a | (intros; apply GlobalTheory.CompanionTheory.RSq.f3a <;> assumption)
