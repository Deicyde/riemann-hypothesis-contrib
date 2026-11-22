module

public import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.ExpEqOfHasDerivAt
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import GroundTheory.AutomorphicForms.RealGroupsIwasawa
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Matrix
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

namespace GroundTheory.Automorphic.ArchWhittakerC

open Matrix MeasureTheory

noncomputable instance : MeasurableSpace U2 := borel U2

instance : BorelSpace U2 := ⟨rfl⟩

noncomputable def μK : Measure U2 := Measure.haarMeasure ⊤

instance : μK.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _

instance : IsProbabilityMeasure μK := ⟨by
  have := Measure.haarMeasure_self (G := U2) (K₀ := ⊤)
  simpa [μK] using this⟩

instance : μK.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  haveI : (Measure.map (· * g) μK).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right μK g
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

instance : μK.IsInvInvariant := by
  refine ⟨?_⟩
  haveI : μK.inv.IsHaarMeasure :=
    { lt_top_of_isCompact := fun K hK => by
        rw [Measure.inv_apply]; exact hK.inv.measure_lt_top
      toIsOpenPosMeasure := ⟨fun U hU hne => by
        rw [Measure.inv_apply]; exact hU.inv.measure_ne_zero μK (by simpa using hne)⟩ }
  haveI : IsProbabilityMeasure μK.inv := by
    rw [Measure.inv]
    infer_instance
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem integral_mul_left_K {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : U2 → E)
    (g : U2) : ∫ k, f (g * k) ∂μK = ∫ k, f k ∂μK :=
  integral_mul_left_eq_self f g

theorem integral_mul_right_K {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : U2 → E)
    (g : U2) : ∫ k, f (k * g) ∂μK = ∫ k, f k ∂μK :=
  integral_mul_right_eq_self f g

theorem integral_inv_K {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : U2 → E) :
    ∫ k, f k⁻¹ ∂μK = ∫ k, f k ∂μK :=
  integral_inv_eq_self f μK

end GroundTheory.Automorphic.ArchWhittakerC
