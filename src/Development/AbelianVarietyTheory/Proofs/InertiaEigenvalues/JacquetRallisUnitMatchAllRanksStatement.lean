module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchAllRanks
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_all_ranks : ∀ r, UnitMatch r := by
  exact @GlobalTheory.JR.unitMatch_all
