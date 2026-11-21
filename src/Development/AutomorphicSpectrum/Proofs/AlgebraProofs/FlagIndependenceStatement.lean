module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_independence : GroundTheory.Heights₂.Heights.NumbersDVR.FlagIndependence.Statement := by
  exact @GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main
