module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstCoeffOperatorLinearSubstitutionProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

@[expose] public section

open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constCoeffOperatorLinearSubstitution_proof : LinSt := by
  exact @GlobalTheory.IsoTriv.linSt_holds
