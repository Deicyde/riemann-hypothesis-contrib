module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryLeviSummationGeometricSeries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_levi_summation_geometric_series : Step := by
  exact @GlobalTheory.InertZeta.step
