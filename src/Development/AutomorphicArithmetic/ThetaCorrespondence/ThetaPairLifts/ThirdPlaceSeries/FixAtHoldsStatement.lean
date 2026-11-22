module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjFixAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjTwOfOne
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FixAtHolds

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

theorem _root_.GlobalTheory.T.twisted_conj_fix_at' : GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwConj.FixedPointCondition := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TwConj.fixAt_holds_alt | exact _root_.GlobalTheory.BigOn.Exp.TwConj.fixAt_holds_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.TwConj.fixAt_holds_alt <;> assumption)
end
