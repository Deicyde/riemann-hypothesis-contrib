module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceBoundTuple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealTwLe
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatStHolds

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

theorem _root_.GlobalTheory.T.tuple_flat_estimate : _root_.GlobalTheory.BigOn.Exp.TupLe.FlatCondition := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TupLe.flatSt_holds_alt | exact _root_.GlobalTheory.BigOn.Exp.TupLe.flatSt_holds_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.TupLe.flatSt_holds_alt <;> assumption)
end
