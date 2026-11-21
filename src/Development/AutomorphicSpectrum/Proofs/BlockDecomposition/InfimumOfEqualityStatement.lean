module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfimumOfEquality
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

@[expose] public section

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infimum_of_equality : GlobalTheory.CompanionTheory.EGlue.InfOfEq := by
  exact @GlobalTheory.CompanionTheory.EGlue.infOfEq_holds
