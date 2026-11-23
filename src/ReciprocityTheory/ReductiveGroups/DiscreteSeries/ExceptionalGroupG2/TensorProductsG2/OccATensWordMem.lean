module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.CoefOfEmb
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.IsSmoothL2OfCasimirEigen
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.ContinuousUnitaryMatrix
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.OccATensWordMem

@[expose] public section

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

section Ambient

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem occA_tensGrp_mul (dual : Bool) (hσ : IsURepOn (UJset ε) σ) {g k : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (hk : k ∈ Kset ε) (f : Fin n → H) :
    tensGrp dual σ (g * k) f = tensGrp dual σ g (kDiag dual σ k f) := by
  exact tensor_group_mul_kDiag dual hσ hg hk f

theorem occA_coef_smooth (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (η f : Fin n → H)
    (hf : ∀ d, IsSmoothVecU ε σ (f d)) : Formalism.REAL.SmoothOnG ε (occCoef dual σ η f) := by
  exact tensor_coef_smooth dual η f hf

theorem occA_coef_memLp (dual : Bool) (hσ : IsURepOn (UJset ε) σ) {S : Submodule ℂ D}
    (hW : ∀ v ∈ S, ∀ w ∈ S, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (η f : Fin n → D) (hη : η ∈ tensSub S) (hf : f ∈ tensSub S) :
    MemLp (fun g : Formalism.REAL.UJ ε =>
      occCoef dual σ (fun c => (η c : H)) (fun c => (f c : H)) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
  exact tensor_coef_memLp dual hσ hW η f hη hf

end Ambient

end ReciprocityTheory.ChartRestriction.DS.G2
