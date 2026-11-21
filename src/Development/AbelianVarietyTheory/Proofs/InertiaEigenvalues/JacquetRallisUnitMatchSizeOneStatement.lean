module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSizeOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_sizeOne : UnitMatch 0 := by
  exact @GlobalTheory.JR.SizeOne.unitMatch_zero
