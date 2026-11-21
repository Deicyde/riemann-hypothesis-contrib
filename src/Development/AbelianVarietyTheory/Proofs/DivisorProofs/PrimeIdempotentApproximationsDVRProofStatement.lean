module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeIdempotentApproximationsDVRProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

@[expose] public section

open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primeIdempotentApproximationsDVR_proof : EpsSt := by
  exact @GlobalTheory.IsoTriv.PrimeIdempotent.epsSt
