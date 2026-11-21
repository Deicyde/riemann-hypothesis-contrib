module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActionLinearLogCoordinatesIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

@[expose] public section

open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.action_linear_logCoordinates_integral : ActSt := by
  exact @GlobalTheory.IsoTriv.actSt
