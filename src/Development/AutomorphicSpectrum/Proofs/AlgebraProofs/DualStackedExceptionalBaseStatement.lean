module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalBase
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcChart

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_stacked_exceptional_base : GroundTheory.Heights₂.Heights.DualStackedExcBase.Statement := by
  exact @GlobalTheory.CompanionTheory.Ar.Giv.exc_base
