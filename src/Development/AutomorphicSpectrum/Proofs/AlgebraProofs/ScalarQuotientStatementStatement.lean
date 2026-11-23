module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ScalarQuotientStatement
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_quotient_statement : GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient.Statement := by
  exact @GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags.main
