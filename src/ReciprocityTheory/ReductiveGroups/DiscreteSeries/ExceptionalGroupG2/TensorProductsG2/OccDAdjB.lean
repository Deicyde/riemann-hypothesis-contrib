module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccDAdjA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccCExistsPs
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Unitarize
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.OccDAdjB

@[expose] public section

noncomputable section

open Finset
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

section Amb

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem adjB_star_Kset {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : kᴴ ∈ Kset ε := by
  refine ⟨?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hk.1
  · have h := congrArg Matrix.conjTranspose hk.2
    simp only [Matrix.conjTranspose_mul] at h
    have hJ : (Jm ε)ᴴ = Jm ε := by
      rw [Jm, Matrix.diagonal_conjTranspose]
      congr 1
      ext a
      exact adjSg_conj ε a
    rw [hJ] at h
    exact h.symm

theorem adjB_inner (hσ : IsURepOn (UJset ε) σ) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (v w : H) :
    inner ℂ (σ k v) w = inner ℂ v (σ kᴴ w) := by
  have hkU : k ∈ UJset ε := smd_inUJ_of_Kset hk
  have hkhU : kᴴ ∈ UJset ε := smd_inUJ_of_Kset (adjB_star_Kset hk)
  have hkk : k * kᴴ = 1 := by
    have := hk.1
    rw [Matrix.mem_unitaryGroup_iff] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  have hinv : σ k (σ kᴴ w) = w := by
    have := hσ.1.2 k hkU kᴴ hkhU
    rw [hkk, hσ.1.1] at this
    exact (congrArg (fun T : H →L[ℂ] H => T w) this).symm
  conv_lhs => rw [← hinv]
  exact inner_map_map_of_isURep hσ hkU v (σ kᴴ w)

end Amb

end ReciprocityTheory.ChartRestriction.DS.G2
