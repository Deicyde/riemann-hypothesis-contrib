module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesCoeffUniformlyContinuousInCoeffsProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

@[expose] public section

open GlobalTheory.IsoTriv

theorem _root_.GlobalTheory.T.seriesCoeffUniformlyContinuousInCoeffs_proof : ContSt := by
  first | exact @GlobalTheory.IsoTriv.contSt_holds | exact GlobalTheory.IsoTriv.contSt_holds | (intros; apply GlobalTheory.IsoTriv.contSt_holds <;> assumption)
