module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylHighestWeightRestrictionBlockDiagonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

@[expose] public section

open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_highest_weight_restriction_blockDiagonal : GlobalTheory.LeviCut.ResHw := by
  exact @GlobalTheory.LeviCut.resHw_holds
