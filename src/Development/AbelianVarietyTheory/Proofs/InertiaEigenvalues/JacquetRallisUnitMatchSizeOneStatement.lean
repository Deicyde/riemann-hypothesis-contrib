module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSizeOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_sizeOne : UnitMatch 0 := by
  first | exact @GlobalTheory.JR.SizeOne.unitMatch_zero | exact GlobalTheory.JR.SizeOne.unitMatch_zero | (intros; apply GlobalTheory.JR.SizeOne.unitMatch_zero <;> assumption)
