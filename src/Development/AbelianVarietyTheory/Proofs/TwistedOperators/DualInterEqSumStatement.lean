module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DualInterEqSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_inter_eq_sum' : Dual := by
  exact @GlobalTheory.InertZeta.dual_inter_eq_sum
