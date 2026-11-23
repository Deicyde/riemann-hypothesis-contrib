module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaD
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaE
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaG
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaF

@[expose] public section

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

section Core

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem tf_ph_memLp (dual : Bool) {lam : Fin n → ℝ} [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε))
    {y : D} (hy : y ∈ genSub E V) {f : Fin n → D} (hf : f ∈ tensSub (genSub E V)) (c : Fin n) :
    MemLp (fun g : Formalism.REAL.UJ ε => coefMap dual σ (Pi.single c (tfSgn ε c • (y : H)))
      (fun d => ((f d : D) : H)) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
  have h := ((coef_embed dual hσ hD hsm hgap hV hc hVK hW _ (tf_single_smul_mem c (tfSgn ε c) hy) f hf).1).2 []
  rw [tf_coe_single] at h
  exact h

end Core

end ReciprocityTheory.ChartRestriction.DS.G2
