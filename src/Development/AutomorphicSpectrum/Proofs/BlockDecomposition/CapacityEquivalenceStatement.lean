module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapacityEquivalence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

@[expose] public section

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capacity_equivalence : GlobalTheory.CompanionTheory.EGlue.CapEquiv := by
  exact @GlobalTheory.CompanionTheory.EGlue.capEquiv
