module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointActionEndomorphismWeightBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

@[expose] public section

open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoint_action_endomorphism_weight_bound : GlobalTheory.LeviCut.AdjBdd := by
  exact @GlobalTheory.LeviCut.adjBdd_holds
