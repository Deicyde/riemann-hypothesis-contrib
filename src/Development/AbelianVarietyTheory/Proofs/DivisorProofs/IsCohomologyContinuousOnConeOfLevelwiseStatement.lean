module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCohomologyContinuousOnConeOfLevelwise
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.isCohomologyContinuousOnCone_of_levelwise : ∀ (R : Type) [CommRing R] (F : Shv R) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Spc) (c : Cone G), (∀ k : SimplexCategoryᵒᵖ, ContCone R F (((evaluation _ PSh).obj k ⋙ disc).mapCone c)) → ContCone R F c := by
  first | (exact @GlobalTheory.EtC.contCone_of_levelwise) | (exact GlobalTheory.EtC.contCone_of_levelwise) | (intros; apply GlobalTheory.EtC.contCone_of_levelwise <;> assumption)
