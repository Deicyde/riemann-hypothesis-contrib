module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitActionLieAlgebraOfPrimeIdempotentApprox
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

@[expose] public section

open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limitActionLieAlgebra_of_primeIdempotentApprox : EpsSt → LimActSt := by
  exact @GlobalTheory.IsoTriv.limActSt_of_epsSt
