module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelThetaTransformationLawMul
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel

@[expose] public section

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelThetaTransformationLaw_mul : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (σ σ' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → σ' ∈ Matrix.symplecticGroup ι ℚ → ∀ φ ψ χ : Matrix κ ι ℚ → ℂ, TransS σ φ ψ → TransS σ' ψ χ → TransS (σ' * σ) φ χ := by
  exact @GlobalTheory.SW.transS_comp
