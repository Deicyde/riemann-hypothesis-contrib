module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReducedFreeAlgebraTraceFormPerfect
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

@[expose] public section

open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduced_free_algebra_traceForm_perfect : GlobalTheory.RegSS.TracePerfect := by
  exact @GlobalTheory.RegSS.tracePerfect
