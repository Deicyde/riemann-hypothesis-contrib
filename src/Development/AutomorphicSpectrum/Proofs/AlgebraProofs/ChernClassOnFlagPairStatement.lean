module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChernClassOnFlagPair
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Inhabit

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_class_on_flag_pair : GroundTheory.Heights₂.Heights.NumbersDVR.ChernClassOnFlagPair.Statement := by
  exact @GlobalTheory.CompanionTheory.ChernFlagPairRootPolynomial.main
