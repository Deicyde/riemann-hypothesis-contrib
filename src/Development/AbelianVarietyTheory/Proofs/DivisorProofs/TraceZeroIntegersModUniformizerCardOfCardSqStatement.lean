module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceZeroIntegersModUniformizerCardOfCardSq
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceZeroIntegersModUniformizerCard_of_cardSq : GlobalTheory.SatakeWeyl.IntIndex → GlobalTheory.SatakeWeyl.TraceZeroIndex := by
  exact @GlobalTheory.SatakeWeyl.traceZeroIndex_of_intIndex
