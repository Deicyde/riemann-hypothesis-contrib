module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagPlainValueIndependent
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerAlt

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_plain_value_independent : GroundTheory.Heights₂.Heights.NumbersDVR.FlagPlainValueIndependence.Statement := by
  exact @GlobalTheory.CompanionTheory.CommAlg.FlagPlainValue.main
