module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ScalarQuotientStatement
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles

@[expose] public section


theorem _root_.GlobalTheory.T.scalar_quotient_statement : GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags.main | exact GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags.main <;> assumption)
