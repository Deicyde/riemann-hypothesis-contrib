module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjCoefAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjTwOfOne
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoefAtOfTwAdm

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

theorem _root_.GlobalTheory.T.twisted_conj_coef_at' : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwConj.CoefficientCondition := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TwConj.coefAt_of_twAdm_alt | exact _root_.GlobalTheory.BigOn.Exp.TwConj.coefAt_of_twAdm_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.TwConj.coefAt_of_twAdm_alt <;> assumption)
end
