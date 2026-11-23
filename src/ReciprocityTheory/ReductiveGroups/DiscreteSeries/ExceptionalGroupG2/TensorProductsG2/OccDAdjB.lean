module

public import Mathlib.Analysis.InnerProductSpace.Subspace
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccDAdjA
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
