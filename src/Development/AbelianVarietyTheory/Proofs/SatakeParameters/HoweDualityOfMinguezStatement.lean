module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweDualityOfMinguez
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howe_duality_of_minguez : GlobalTheory.Published.MinguezThetaGL → GlobalTheory.Published.HoweDualityGL := by
  exact @GlobalTheory.HoweBridge.main
