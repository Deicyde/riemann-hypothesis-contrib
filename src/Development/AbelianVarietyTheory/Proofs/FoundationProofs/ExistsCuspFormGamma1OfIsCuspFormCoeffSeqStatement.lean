module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFormGamma1OfIsCuspFormCoeffSeq
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspForm_gamma1_of_isCuspFormCoeffSeq : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → CF k L (ch ε) a → ∃ f : CuspForm (Gamma1 L) (k : ℤ), ⇑f = qs a := by
  exact @GlobalTheory.EisM.cuspForm_of_CF
