module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserUnitaryGroupHasGaugeMeasure
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushCut

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabiliser_unitaryGroup_has_gaugeMeasure : PI.RhsWLim.W.GaugeK := by
  exact @GlobalTheory.GaugeKExists.gaugeK
