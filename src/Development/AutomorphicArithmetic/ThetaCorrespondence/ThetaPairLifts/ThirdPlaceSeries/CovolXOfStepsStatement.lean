module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFromGramAndBounds
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CovolXOfSteps

@[expose] public section



section
open GlobalTheory.CovTop GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.covolX_of_truncation_badSet_lambda_lowBound : _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftRecursive → _root_.GlobalTheory.CovTop.LiftTruncation → _root_.GlobalTheory.CovTop.LiftBadSet → _root_.GlobalTheory.CovTop.LiftLambdaBound → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoreBound' → _root_.GlobalTheory.CovTop.LiftLowBound → _root_.GlobalTheory.CovTop.CovolumeBoundOfX := by
  first | exact @_root_.GlobalTheory.CovTop.Assembly.covolX_of_lift_bounds_and_coreLe | exact _root_.GlobalTheory.CovTop.Assembly.covolX_of_lift_bounds_and_coreLe | (intros; apply _root_.GlobalTheory.CovTop.Assembly.covolX_of_lift_bounds_and_coreLe <;> assumption)
end
