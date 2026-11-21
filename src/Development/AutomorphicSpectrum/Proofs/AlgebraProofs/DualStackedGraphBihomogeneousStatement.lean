module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedGraphBihomogeneous
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcLead

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_stacked_graph_bihomogeneous : GroundTheory.Heights₂.Heights.DualStackedGraphBihomog.Statement := by
  exact @GlobalTheory.CompanionTheory.Ar.Giv.graph_bihomog
