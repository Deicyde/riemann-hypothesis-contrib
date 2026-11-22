module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShapeIntegratedOperatorRangesPolynomial
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape

@[expose] public section


theorem _root_.GlobalTheory.T.shapeIntegratedOperator_ranges_polynomial : GlobalTheory.PsCo.Pc3.RangeShape := by
  first | exact @GlobalTheory.PsCo.Pc3.rangeShape | exact GlobalTheory.PsCo.Pc3.rangeShape | (intros; apply GlobalTheory.PsCo.Pc3.rangeShape <;> assumption)
