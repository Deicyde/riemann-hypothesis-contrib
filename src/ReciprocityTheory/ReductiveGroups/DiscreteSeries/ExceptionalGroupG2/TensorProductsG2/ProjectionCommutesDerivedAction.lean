module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccATensWordMem
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccBLowKShiftF
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ImageLeClosGen
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.ProjectionCommutesDerivedAction

@[expose] public section

noncomputable section

open Finset MeasureTheory
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

section Proj

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem projection_commutes_right_regular (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    ∀ g ∈ UJset ε, ∀ v : L2 ε,
      (Hlam ε Ψ v₀).starProjection (rreg ε g v) = rreg ε g ((Hlam ε Ψ v₀).starProjection v) := by
  intro g hg v
  have h := Lap.QuotA.proj_comm (rreg_isURepOn ε) (Hlam ε Ψ v₀) (rreg_mem_Hlam hgap hP hv₀) g hg v
  rw [Submodule.starProjection_orthogonal'] at h
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, map_sub] at h
  exact sub_right_injective h

theorem projection_preserves_smooth (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (x : L2 ε)
    (hx : x ∈ smD ε (rreg ε)) : (Hlam ε Ψ v₀).starProjection x ∈ smD ε (rreg ε) :=
  Lap.QuotA.smooth_of_comm _ (fun g hg v => projection_commutes_right_regular hgap hP hv₀ g hg v) hx

theorem projection_commutes_derived_action (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (x : smD ε (rreg ε))
    (hx : (Hlam ε Ψ v₀).starProjection (x : L2 ε) ∈ smD ε (rreg ε)) (a b : Fin n) :
    ((smE ε (rreg ε) a b ⟨(Hlam ε Ψ v₀).starProjection (x : L2 ε), hx⟩ : smD ε (rreg ε)) : L2 ε) =
      (Hlam ε Ψ v₀).starProjection ((smE ε (rreg ε) a b x : smD ε (rreg ε)) : L2 ε) :=
  Lap.QuotA.smE_comm (rreg_isURepOn ε) _ (fun g hg v => projection_commutes_right_regular hgap hP hv₀ g hg v) x hx a b

end Proj

end ReciprocityTheory.ChartRestriction.DS.G2
