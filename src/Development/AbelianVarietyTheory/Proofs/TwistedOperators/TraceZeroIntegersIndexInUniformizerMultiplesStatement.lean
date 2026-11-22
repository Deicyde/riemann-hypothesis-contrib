module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceZeroIntegersIndexInUniformizerMultiples
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.traceZero_integers_index_in_uniformizer_multiples : TraceIndex := by
  first | exact @GlobalTheory.InertZeta.traceIndex | exact GlobalTheory.InertZeta.traceIndex | (intros; apply GlobalTheory.InertZeta.traceIndex <;> assumption)
