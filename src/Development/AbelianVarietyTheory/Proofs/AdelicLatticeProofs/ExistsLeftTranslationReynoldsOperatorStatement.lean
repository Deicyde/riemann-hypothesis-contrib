module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsLeftTranslationReynoldsOperator
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_leftTranslation_reynoldsOperator : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∃ Rey, IsReynolds Γ Rey := by
  exact @GlobalTheory.ClassFin.ReynoldsLtr.exists_isReynolds
