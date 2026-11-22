module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyLocalObjectsExistAtTermsProof
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude

@[expose] public section


theorem _root_.GlobalTheory.T.familyLocalObjectsExistAtTerms_proof : GlobalTheory.SnFam.ExistFam := by
  first | exact @GlobalTheory.SnFam.existFam | exact GlobalTheory.SnFam.existFam | (intros; apply GlobalTheory.SnFam.existFam <;> assumption)
