module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoConsecutiveProjectorInvariance
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

@[expose] public section

open GlobalTheory.LeviCut

theorem _root_.GlobalTheory.T.rank_two_consecutive_projector_invariance : GlobalTheory.LeviCut.RankTwo := by
  first | exact @GlobalTheory.LeviCut.RankTwoProof.rankTwo | exact GlobalTheory.LeviCut.RankTwoProof.rankTwo | (intros; apply GlobalTheory.LeviCut.RankTwoProof.rankTwo <;> assumption)
