module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonGaugeBiadditiveOfLogSumActionLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

@[expose] public section

open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonGaugeBiadditive_of_logSum_actionLinear : AddSt → ActSt → BiaddSt := by
  exact @GlobalTheory.IsoTriv.GaugeBiadd.biadd_of_add_of_act
