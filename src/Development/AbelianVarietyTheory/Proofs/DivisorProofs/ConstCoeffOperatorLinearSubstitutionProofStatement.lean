module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstCoeffOperatorLinearSubstitutionProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

@[expose] public section

open GlobalTheory.IsoTriv

theorem _root_.GlobalTheory.T.constCoeffOperatorLinearSubstitution_proof : LinSt := by
  first | exact @GlobalTheory.IsoTriv.linSt_holds | exact GlobalTheory.IsoTriv.linSt_holds | (intros; apply GlobalTheory.IsoTriv.linSt_holds <;> assumption)
