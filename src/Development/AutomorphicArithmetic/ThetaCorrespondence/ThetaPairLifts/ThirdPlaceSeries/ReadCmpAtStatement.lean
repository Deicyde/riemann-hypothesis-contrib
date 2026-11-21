module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonReadableAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadComparisonAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadCmpAt

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.readCmpAt_of_serBase : _root_.GlobalTheory.BigOn.Exp.SerBase.ReadComparisonAt := by
  exact @_root_.GlobalTheory.BigOn.Exp.SerBase.readCmpAt_alt
end
