module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelJoinRight
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExSubAlt

@[expose] public section


theorem _root_.GlobalTheory.T.flag_model_join_right : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinRightAlt.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight.main | exact GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight.main <;> assumption)
