module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFlagBundlePushForwardFormula
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality

@[expose] public section


theorem _root_.GlobalTheory.T.fullFlagBundle_pushForward_formula : GlobalTheory.Published.FlagPushForward := by
  first | exact @GlobalTheory.FlagPushProof.flagPushForward | exact GlobalTheory.FlagPushProof.flagPushForward | (intros; apply GlobalTheory.FlagPushProof.flagPushForward <;> assumption)
