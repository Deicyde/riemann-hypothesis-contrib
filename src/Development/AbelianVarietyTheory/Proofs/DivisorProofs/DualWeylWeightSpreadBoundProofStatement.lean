module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylWeightSpreadBoundProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

@[expose] public section

open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylWeightSpreadBound_proof : GlobalTheory.LeviCut.NablaBdd := by
  exact @GlobalTheory.LeviCut.nablaBdd
