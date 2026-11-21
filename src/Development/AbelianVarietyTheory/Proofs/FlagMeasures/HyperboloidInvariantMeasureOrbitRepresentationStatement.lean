module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidInvariantMeasureOrbitRepresentation
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushCut

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperboloid_invariant_measure_orbit_representation : PI.RhsWLim.W.OrbRepY := by
  exact @GlobalTheory.HypOrbitUnique.orbRepY
