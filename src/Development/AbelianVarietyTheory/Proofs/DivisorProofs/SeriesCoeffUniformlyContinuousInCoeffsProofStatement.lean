module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesCoeffUniformlyContinuousInCoeffsProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

@[expose] public section

open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seriesCoeffUniformlyContinuousInCoeffs_proof : ContSt := by
  exact @GlobalTheory.IsoTriv.contSt_holds
