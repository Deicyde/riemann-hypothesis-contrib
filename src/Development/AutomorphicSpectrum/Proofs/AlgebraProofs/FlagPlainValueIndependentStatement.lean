module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagPlainValueIndependent
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerAlt

@[expose] public section


theorem _root_.GlobalTheory.T.flag_plain_value_independent : GroundTheory.Heights₂.Heights.NumbersDVR.FlagPlainValueIndependence.Statement := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.FlagPlainValue.main | exact GlobalTheory.CompanionTheory.CommAlg.FlagPlainValue.main | (intros; apply GlobalTheory.CompanionTheory.CommAlg.FlagPlainValue.main <;> assumption)
