module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemGeneralLemmaAllOrders
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm

@[expose] public section

open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveSystem_generalLemma_all_orders : ∀ N : ℕ, GLOnto N ∧ GLCount N := by
  exact @GlobalTheory.PMonE.generalLemma_allOrders
