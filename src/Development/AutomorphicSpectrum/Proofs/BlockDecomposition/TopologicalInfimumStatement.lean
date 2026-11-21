module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopologicalInfimum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

@[expose] public section

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topological_infimum : GlobalTheory.CompanionTheory.EGlue.TopInf := by
  exact @GlobalTheory.CompanionTheory.EGlue.Gl0.topInf
