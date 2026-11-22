module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HTChartExistsHolds
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HTChartExists

@[expose] public section


theorem _root_.GlobalTheory.T.HTChartExists_holds : GlobalTheory.CompanionTheory.Ar.BT.HTChartExists := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.ChartEx.htChartExists | exact GlobalTheory.CompanionTheory.Ar.BT.ChartEx.htChartExists | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.ChartEx.htChartExists <;> assumption)
