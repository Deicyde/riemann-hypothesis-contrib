module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSecondStep
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

@[expose] public section

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_second_step : GlobalTheory.CompanionTheory.EGlue.PairSlices → GlobalTheory.CompanionTheory.EGlue.PairStep₂ := by
  exact @GlobalTheory.CompanionTheory.EGlue.pairStep₂
