module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerTubeGaugeMassAsymptotic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushCut

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizerTube_gaugeMass_asymptotic : PI.RhsWLim.W.TubeLimK := by
  exact @GlobalTheory.StabTube.tubeLimK
