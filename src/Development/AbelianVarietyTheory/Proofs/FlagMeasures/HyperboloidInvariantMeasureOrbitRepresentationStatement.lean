module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidInvariantMeasureOrbitRepresentation
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushCut

@[expose] public section


theorem _root_.GlobalTheory.T.hyperboloid_invariant_measure_orbit_representation : PI.RhsWLim.W.OrbRepY := by
  first | exact @GlobalTheory.HypOrbitUnique.orbRepY | exact GlobalTheory.HypOrbitUnique.orbRepY | (intros; apply GlobalTheory.HypOrbitUnique.orbRepY <;> assumption)
