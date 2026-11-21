module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankThreeRootIndexOfCards
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRankThreeRootIndex_of_cards : GlobalTheory.SatakeWeyl.IntIndex → GlobalTheory.SatakeWeyl.TraceZeroIndex → GlobalTheory.SatakeWeyl.IndexThree := by
  exact @GlobalTheory.SatakeWeyl.Heis.indexThree
