module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.StokesLimitStatementHolds
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesLimitTVb

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stokes_limit_statement_holds : GroundTheory.Heights₂.Heights.LowerBoundFree.StokesLimitTVb.Statement := by
  exact @GlobalTheory.CompanionTheory.Ar.Giv.VbLimit.stokesLimitTVb
