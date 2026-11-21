module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatThetaQuotientAtPrincipalLevelProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatThetaQuotientAtPrincipalLevel_proof : GlobalTheory.BaseCmp.FlatTwoStep := by
  exact @GlobalTheory.BaseCmp.flatTwoStep_holds
