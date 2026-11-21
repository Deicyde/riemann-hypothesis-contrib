module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimalBlowupSmoothWithSemiAbelianCharts
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimalBlowup_smooth_with_semiAbelianCharts : GlobalTheory.SiegJoin.ChartSt5 := by
  exact @GlobalTheory.SiegJoin.chartSt5_holds
