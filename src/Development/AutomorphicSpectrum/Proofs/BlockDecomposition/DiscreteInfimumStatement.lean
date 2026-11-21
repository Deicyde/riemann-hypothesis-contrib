module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiscreteInfimum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

@[expose] public section

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_infimum : GlobalTheory.CompanionTheory.EGlue.DiscInf := by
  exact @GlobalTheory.CompanionTheory.EGlue.discInf
