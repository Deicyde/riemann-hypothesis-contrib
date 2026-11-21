module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarUnitaryGroupWbDensityChart
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.GaugeExists

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_unitaryGroupWb_density_chart : PI.RhsWLim.W.HaarDens := by
  exact @GlobalTheory.HaarDensChart.haarDens
