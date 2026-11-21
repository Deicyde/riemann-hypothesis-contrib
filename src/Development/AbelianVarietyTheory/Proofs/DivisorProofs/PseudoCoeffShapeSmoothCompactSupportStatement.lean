module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoeffShapeSmoothCompactSupport
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape

@[expose] public section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pseudoCoeffShape_smooth_compactSupport : GlobalTheory.PsCo.Pc1.StShape := by
  exact @GlobalTheory.ShapeSmoothFinite.stShape
