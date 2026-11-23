module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.CoefOfEmb
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IntegrableComplexContinuousBoundedSupport
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.ContinuousUnitaryMatrix
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
