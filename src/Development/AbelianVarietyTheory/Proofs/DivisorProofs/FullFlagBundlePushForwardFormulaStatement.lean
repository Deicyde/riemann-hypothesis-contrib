module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFlagBundlePushForwardFormula
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullFlagBundle_pushForward_formula : GlobalTheory.Published.FlagPushForward := by
  exact @GlobalTheory.FlagPushProof.flagPushForward
