module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmSumIntegralAdditive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

@[expose] public section

open GlobalTheory.IsoTriv

theorem _root_.GlobalTheory.T.logarithm_sum_integral_additive : AddSt := by
  first | exact @GlobalTheory.IsoTriv.log_sum_additive_preserves_integrality | exact GlobalTheory.IsoTriv.log_sum_additive_preserves_integrality | (intros; apply GlobalTheory.IsoTriv.log_sum_additive_preserves_integrality <;> assumption)
