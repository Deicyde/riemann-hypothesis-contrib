module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section


theorem _root_.GlobalTheory.T.theta_action_exists : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.ActsEx := by
  first | exact @GlobalTheory.ThK.LocalOps.actsEx | exact GlobalTheory.ThK.LocalOps.actsEx | (intros; apply GlobalTheory.ThK.LocalOps.actsEx <;> assumption)
