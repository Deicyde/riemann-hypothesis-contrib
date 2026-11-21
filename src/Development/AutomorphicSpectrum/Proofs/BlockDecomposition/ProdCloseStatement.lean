module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdClose
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

@[expose] public section

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_facts_alt : GlobalTheory.CompanionTheory.EGlue.MCloseFacts := by
  exact @GlobalTheory.CompanionTheory.EGlue.mCloseFacts_holds
