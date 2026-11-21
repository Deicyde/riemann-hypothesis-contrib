module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PullbackConeNullModPHolds
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullConeNullModP

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_cone_null_mod_p_holds : GroundTheory.Heights₂.Heights.HilbertSamuel.PullConeNullModP.Statement := by
  exact @GlobalTheory.CompanionTheory.Ar.Giv.pullConeNullModP
