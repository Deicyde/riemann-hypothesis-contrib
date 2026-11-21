module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceType
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

@[expose] public section

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slice_type : GlobalTheory.CompanionTheory.EGlue.SliceType := by
  exact @GlobalTheory.CompanionTheory.EGlue.SliceTypePf.main
