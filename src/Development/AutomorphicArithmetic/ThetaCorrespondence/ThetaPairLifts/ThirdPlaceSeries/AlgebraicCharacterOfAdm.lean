module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicCharacterOfAdm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltAltBis

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.algebraicCharacter_of_adm2 : ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → GlobalTheory.JumpDictionaryFoundation.AlgebraicCharacter_at D := by
  first | exact @_root_.GlobalTheory.AlgCharFromGal.main_alt_alt_alt | exact _root_.GlobalTheory.AlgCharFromGal.main_alt_alt_alt | (intros; apply _root_.GlobalTheory.AlgCharFromGal.main_alt_alt_alt <;> assumption)
end
