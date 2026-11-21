module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneProjectorWeightZeroInvariance
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

@[expose] public section

open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_projector_weight_zero_invariance : GlobalTheory.LeviCut.RankOne := by
  exact @GlobalTheory.LeviCut.rankOne
