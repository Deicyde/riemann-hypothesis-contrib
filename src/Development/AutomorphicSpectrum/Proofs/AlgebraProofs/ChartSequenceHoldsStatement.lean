module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartSequenceHolds
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane

@[expose] public section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_sequence_holds : ChartSequence := by
  exact @GlobalTheory.CompanionTheory.Ar.HT.FinrankDualChartSequence.chartSequence
