module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDescentEstimate
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DesPol

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun

theorem _root_.GlobalTheory.T.polynomial_descent_estimate' : _root_.GlobalTheory.BigTop.Fun.DescentPolynomialCondition := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.desPol_alt | exact _root_.GlobalTheory.BigTop.Fun.desPol_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.desPol_alt <;> assumption)
end
