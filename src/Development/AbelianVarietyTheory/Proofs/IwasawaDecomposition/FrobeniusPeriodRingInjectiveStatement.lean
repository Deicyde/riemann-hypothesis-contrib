module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_period_ring_injective : ∀ (l : ℕ) [Fact l.Prime], Function.Injective (Per.φB l) := by
  exact @GlobalTheory.MemLoc.phiB_injective
