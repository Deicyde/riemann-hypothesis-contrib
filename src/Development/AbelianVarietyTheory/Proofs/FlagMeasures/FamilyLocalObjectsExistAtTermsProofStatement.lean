module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyLocalObjectsExistAtTermsProof
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyLocalObjectsExistAtTerms_proof : GlobalTheory.SnFam.ExistFam := by
  exact @GlobalTheory.SnFam.existFam
