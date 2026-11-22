module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyNormBoundAbsoluteConstant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta

@[expose] public section


theorem _root_.GlobalTheory.T.normalisedFamily_normBound_absoluteConstant : GlobalTheory.ColNorms.FamilyNorms := by
  first | exact @GlobalTheory.ColNorms.FamilyBound.familyNorms | exact GlobalTheory.ColNorms.FamilyBound.familyNorms | (intros; apply GlobalTheory.ColNorms.FamilyBound.familyNorms <;> assumption)
