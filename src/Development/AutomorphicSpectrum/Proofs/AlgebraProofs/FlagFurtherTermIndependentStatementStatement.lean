module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagFurtherTermIndependentStatement
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisFurther

@[expose] public section


theorem _root_.GlobalTheory.T.flag_further_term_independent_statement : GroundTheory.Heights₂.Heights.NumbersDVR.flagFurtherTerm_independent.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.flag_further_term_independent | exact GlobalTheory.CompanionTheory.Ar.Num.flag_further_term_independent | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.flag_further_term_independent <;> assumption)
