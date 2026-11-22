module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelValueIndependent
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitBis

@[expose] public section


theorem _root_.GlobalTheory.T.flag_model_value_independent : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelValueIndependence.Statement := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.FlagModelValue.main | exact GlobalTheory.CompanionTheory.CommAlg.FlagModelValue.main | (intros; apply GlobalTheory.CompanionTheory.CommAlg.FlagModelValue.main <;> assumption)
