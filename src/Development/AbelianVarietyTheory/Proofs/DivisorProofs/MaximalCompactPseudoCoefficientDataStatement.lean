module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactPseudoCoefficientData
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape

@[expose] public section

open GlobalTheory.PsCo.Pc1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalCompact_pseudoCoefficientData : StKData := by
  exact @GlobalTheory.PsCo.Pc1.maximalCompact_pseudoCoefficientData'
