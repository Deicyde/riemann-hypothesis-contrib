module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

open Complex ArithmeticFunction

noncomputable section

namespace Formalism.ZF

namespace VonMangoldtMertensInequality

lemma re_term_vonMangoldt {n : ℕ} (hn : n ≠ 0) (σ y : ℝ) :
    (LSeries.term (fun m => (Λ m : ℂ)) ((σ : ℂ) + y * I) n).re =
      Λ n * Real.exp (-σ * Real.log n) * Real.cos (y * Real.log n) := by
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, Complex.re_ofReal_mul,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hn), Complex.exp_re]
  simp only [Complex.log_re, Complex.log_im, Complex.norm_natCast, Complex.natCast_arg,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
    zero_mul, add_zero, mul_one]
  rw [mul_assoc, ← Real.cos_neg]; congr 2 <;> ring

lemma hasSum_re_L {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    HasSum (fun n => (LSeries.term (fun m => (Λ m : ℂ)) ((σ : ℂ) + y * I) n).re)
      (-(deriv riemannZeta ((σ : ℂ) + y * I) / riemannZeta ((σ : ℂ) + y * I))).re := by
  have hs : 1 < ((σ : ℂ) + y * I).re := by simp [hσ]
  have h1 := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).LSeriesHasSum
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_div] at h1
  simpa only [Complex.reCLM_apply] using Complex.reCLM.hasSum h1

lemma comb_nonneg (a θ : ℝ) (ha : 0 ≤ a) :
    0 ≤ 3 * a + 4 * (a * Real.cos θ) + a * Real.cos (2 * θ) := by
  rw [Real.cos_two_mul]
  nlinarith [mul_nonneg ha (sq_nonneg (1 + Real.cos θ))]

end VonMangoldtMertensInequality

open VonMangoldtMertensInequality in
theorem mertensInequality : ThreeFourOne := by
  intro σ t hσ
  have hs := (((hasSum_re_L hσ 0).mul_left 3).add ((hasSum_re_L hσ t).mul_left 4)).add (hasSum_re_L hσ (2 * t))
  have key := HasSum.nonneg (fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp only [re_term_vonMangoldt hn, zero_mul, Real.cos_zero, mul_one]
      have ha : 0 ≤ Λ n * Real.exp (-σ * Real.log n) := mul_nonneg vonMangoldt_nonneg (Real.exp_pos _).le
      simpa [mul_assoc] using comb_nonneg _ (t * Real.log n) ha) hs
  simpa [mul_assoc] using key

end Formalism.ZF
