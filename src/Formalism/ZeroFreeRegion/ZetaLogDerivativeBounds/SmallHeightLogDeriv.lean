module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Complex Set Filter Topology

noncomputable section

namespace Formalism.ZF

lemma shld_identity {s : ℂ} (hs : s ≠ 1) (h1 : riemannZeta₁ s ≠ 0) :
    deriv riemannZeta s / riemannZeta s + 1 / (s - 1) =
      deriv riemannZeta₁ s / riemannZeta₁ s := by
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs, riemannZeta_eq_inv_sub_mul hs]
  field_simp; ring

lemma riemannZeta₁_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta₁ s ≠ 0 := by
  intro h
  by_cases hs1 : s = 1
  · subst hs1; simp at h
  · exact riemannZeta_ne_zero_of_one_le_re hs (by rw [riemannZeta_eq_inv_sub_mul hs1, h, mul_zero])

theorem logDerivBoundedHeight : SmallHeightLogDeriv := by
  intro T
  have hK : IsCompact (Icc (1 : ℝ) 3 ×ℂ Icc (-T) T) := isCompact_Icc.reProdIm isCompact_Icc
  have hU : IsOpen {s : ℂ | riemannZeta₁ s ≠ 0} :=
    isOpen_ne_fun differentiable_riemannZeta₁.continuous continuous_const
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_thickening_subset_open hU
    fun _ hs => riemannZeta₁_ne_zero_of_one_le_re (Complex.mem_reProdIm.mp hs).1.1
  have hne : ∀ s : ℂ, |s.im| ≤ T → 1 - δ / 2 ≤ s.re → s.re ≤ 3 → riemannZeta₁ s ≠ 0 := fun s him hre hre3 => by
    by_cases h1 : 1 ≤ s.re
    · exact riemannZeta₁_ne_zero_of_one_le_re h1
    · refine hδU (Metric.mem_thickening_iff.mpr ⟨1 + s.im * I, ?_, ?_⟩)
      · rw [Complex.mem_reProdIm]; obtain ⟨h3, h4⟩ := abs_le.mp him; simp; constructor <;> linarith
      · rw [Complex.dist_eq, show s - (1 + s.im * I) = ((s.re - 1 : ℝ) : ℂ) by apply Complex.ext <;> simp,
          Complex.norm_real, Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  have hcont : ContinuousOn (fun s => deriv riemannZeta₁ s / riemannZeta₁ s)
      (Icc (1 - δ / 2) 3 ×ℂ Icc (-T) T) :=
    ((differentiable_riemannZeta₁.differentiableOn.deriv isOpen_univ).continuousOn.mono (subset_univ _)).div
      differentiable_riemannZeta₁.continuous.continuousOn fun s hs => by
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := Complex.mem_reProdIm.mp hs
        exact hne s (abs_le.mpr ⟨h3, h4⟩) h1 h2
  obtain ⟨C, hC⟩ := (isCompact_Icc.reProdIm isCompact_Icc).exists_bound_of_continuousOn hcont
  refine ⟨δ / 2, C, half_pos hδ, fun s hs him hre hre3 => ?_⟩
  rw [shld_identity hs (hne s him hre hre3)]
  exact hC s (Complex.mem_reProdIm.mpr ⟨⟨hre, hre3⟩, abs_le.mp him⟩)

end Formalism.ZF
