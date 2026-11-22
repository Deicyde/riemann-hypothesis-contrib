module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchorBoundStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AnchorHolds

@[expose] public section



section
open GlobalTheory.CovTop GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.anchor_bound : _root_.GlobalTheory.CovTop.AnchorCondition := by
  first | exact @_root_.GlobalTheory.CovTop.anchor_holds_alt | exact _root_.GlobalTheory.CovTop.anchor_holds_alt | (intros; apply _root_.GlobalTheory.CovTop.anchor_holds_alt <;> assumption)
end
