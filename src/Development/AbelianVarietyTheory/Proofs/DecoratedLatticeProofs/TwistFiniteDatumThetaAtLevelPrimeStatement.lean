module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistFiniteDatumThetaAtLevelPrime
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt

@[expose] public section


theorem _root_.GlobalTheory.T.twistFiniteDatum_theta_at_levelPrime : GlobalTheory.AdForm.TwVec' := by
  first | exact @GlobalTheory.AdForm.twVec' | exact GlobalTheory.AdForm.twVec' | (intros; apply GlobalTheory.AdForm.twVec' <;> assumption)
