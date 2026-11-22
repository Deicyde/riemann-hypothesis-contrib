module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawLeftRestrictionGlobal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealTwLe
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesSt

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

theorem _root_.GlobalTheory.T.seesaw_places_statement : _root_.GlobalTheory.BigOn.Exp.TupLe.PlacesCondition := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TupLe.placesSt_alt | exact _root_.GlobalTheory.BigOn.Exp.TupLe.placesSt_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.TupLe.placesSt_alt <;> assumption)
end
