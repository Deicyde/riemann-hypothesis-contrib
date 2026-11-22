module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedExistence
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdaptEx

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

theorem _root_.GlobalTheory.T.adaptEx' : _root_.GlobalTheory.BigOn.Exp.AdaptedExistence₂ := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.adaptEx_alt | exact _root_.GlobalTheory.BigOn.Exp.adaptEx_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.adaptEx_alt <;> assumption)
end
