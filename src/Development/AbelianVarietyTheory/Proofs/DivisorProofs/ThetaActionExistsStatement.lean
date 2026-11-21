module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_action_exists : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.ActsEx := by
  exact @GlobalTheory.ThK.LocalOps.actsEx
