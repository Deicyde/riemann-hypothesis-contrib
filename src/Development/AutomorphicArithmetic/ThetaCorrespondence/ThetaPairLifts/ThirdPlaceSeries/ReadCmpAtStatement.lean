module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonReadableAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadComparisonAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadCmpAt

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase

theorem _root_.GlobalTheory.T.readCmpAt_of_serBase : _root_.GlobalTheory.BigOn.Exp.SerBase.ReadComparisonAt := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.SerBase.readCmpAt_alt | exact _root_.GlobalTheory.BigOn.Exp.SerBase.readCmpAt_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.SerBase.readCmpAt_alt <;> assumption)
end
