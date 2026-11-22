module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyNonzeroThetaVectorsNumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta

@[expose] public section


theorem _root_.GlobalTheory.T.normalisedFamily_nonzeroThetaVectors_numberField : GlobalTheory.ColNorms.FamilyVectors := by
  first | exact @GlobalTheory.ColNorms.familyVectors | exact GlobalTheory.ColNorms.familyVectors | (intros; apply GlobalTheory.ColNorms.familyVectors <;> assumption)
