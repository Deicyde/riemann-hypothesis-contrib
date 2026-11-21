module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelJoinRight
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExSubAlt

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_model_join_right : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinRightAlt.Statement := by
  exact @GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight.main
