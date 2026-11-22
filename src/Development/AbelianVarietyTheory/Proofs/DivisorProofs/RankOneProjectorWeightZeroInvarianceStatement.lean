module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneProjectorWeightZeroInvariance
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

@[expose] public section

open GlobalTheory.LeviCut

theorem _root_.GlobalTheory.T.rank_one_projector_weight_zero_invariance : GlobalTheory.LeviCut.RankOne := by
  first | exact @GlobalTheory.LeviCut.rankOne | exact GlobalTheory.LeviCut.rankOne | (intros; apply GlobalTheory.LeviCut.rankOne <;> assumption)
