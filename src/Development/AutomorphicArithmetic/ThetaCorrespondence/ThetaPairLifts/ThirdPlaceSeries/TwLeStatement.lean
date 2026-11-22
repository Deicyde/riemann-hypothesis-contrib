module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistUpperBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwLe

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

theorem _root_.GlobalTheory.T.twist_upper_bound_of_prints : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter → _root_.GlobalTheory.BigOn.Exp.TwistUpperBound₂ := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TupLe.twLe_alt | exact _root_.GlobalTheory.BigOn.Exp.TupLe.twLe_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.TupLe.twLe_alt <;> assumption)
end
