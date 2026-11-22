module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalingFunctionBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIntegralMultipleHolds

@[expose] public section



section

theorem _root_.GlobalTheory.T.scaling_function_bound' : _root_.GlobalTheory.BigTop.Fun.ScaleCondition := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.existsIntegralMultiple_holds_alt | exact _root_.GlobalTheory.BigTop.Fun.existsIntegralMultiple_holds_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.existsIntegralMultiple_holds_alt <;> assumption)
end
