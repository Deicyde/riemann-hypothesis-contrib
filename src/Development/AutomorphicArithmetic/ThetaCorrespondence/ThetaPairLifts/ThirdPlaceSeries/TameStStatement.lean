module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameAtSmallPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallnessCondition
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameSt

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

theorem _root_.GlobalTheory.T.tame_at_of_small_at : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → TameAt p j w := by
  first | exact @_root_.GlobalTheory.TameStab.tameSt_alt | exact _root_.GlobalTheory.TameStab.tameSt_alt | (intros; apply _root_.GlobalTheory.TameStab.tameSt_alt <;> assumption)
end
