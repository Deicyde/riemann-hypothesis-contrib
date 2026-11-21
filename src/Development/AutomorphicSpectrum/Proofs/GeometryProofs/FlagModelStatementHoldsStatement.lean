module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagModelStatementHolds
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlagModelStatement

@[expose] public section

open GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.FlagModelStatement_holds : FlagModelStatement := by
  exact @GlobalTheory.CompanionTheory.Ar.FlagModel.flagModel
