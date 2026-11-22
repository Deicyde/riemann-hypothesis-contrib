module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActionLinearLogCoordinatesIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

@[expose] public section

open GlobalTheory.IsoTriv

theorem _root_.GlobalTheory.T.action_linear_logCoordinates_integral : ActSt := by
  first | exact @GlobalTheory.IsoTriv.actSt | exact GlobalTheory.IsoTriv.actSt | (intros; apply GlobalTheory.IsoTriv.actSt <;> assumption)
