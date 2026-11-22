module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseUpperBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSeries

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

theorem _root_.GlobalTheory.T.baseLe_of_cuspRapidDecay_artin_rayClassField : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.BaseUpperBound₂ := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.baseLe_of_cusp_decay_and_ray_class_field | exact _root_.GlobalTheory.BigOn.Exp.baseLe_of_cusp_decay_and_ray_class_field | (intros; apply _root_.GlobalTheory.BigOn.Exp.baseLe_of_cusp_decay_and_ray_class_field <;> assumption)
end
