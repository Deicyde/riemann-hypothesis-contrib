module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyCoeffVectorsLieInFiniteDimensionalSmooth
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape

@[expose] public section


theorem _root_.GlobalTheory.T.polyCoeff_vectors_lie_in_finiteDimensional_smooth : GlobalTheory.PsCo.Pc3.UFin := by
  first | exact @GlobalTheory.PsCo.Pc3.uFin | exact GlobalTheory.PsCo.Pc3.uFin | (intros; apply GlobalTheory.PsCo.Pc3.uFin <;> assumption)
