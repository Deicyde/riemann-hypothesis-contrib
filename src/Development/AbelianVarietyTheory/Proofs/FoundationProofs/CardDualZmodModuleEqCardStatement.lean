module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCard
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_dual_zmod_module_eq_card : ∀ (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A] [Module (ZMod n) A] [Finite A], Nat.card (Module.Dual (ZMod n) A) = Nat.card A := by
  exact @GlobalTheory.ZModDual.card_dual_eq
