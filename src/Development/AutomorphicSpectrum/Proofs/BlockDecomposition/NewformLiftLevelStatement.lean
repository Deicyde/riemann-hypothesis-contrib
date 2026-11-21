module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevel
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_lift_level : Ad3.R.B0 → Ad3.R.F1 := by
  exact @GlobalTheory.CompanionTheory.RSLift.adelic_lift_exists
