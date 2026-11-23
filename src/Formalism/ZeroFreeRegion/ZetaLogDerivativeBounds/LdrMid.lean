module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LdrInvSubOneLe
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZfoGrowthBall
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

open Complex Metric

noncomputable section

namespace Formalism.ZF

lemma ldr_mid {c₀ : ℝ}
    (hZ0 : ∀ s : ℂ, s ≠ 1 → 1 - c₀ / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0)
    (hc₀ : 0 < c₀) (hG : ZetaGrowth) (hI : ZetaInvBound) (hLL : LandauLocal) {σ t : ℝ}
    (hL : 24 ≤ Real.log (|t| + 2))
    (hσlo : 1 - (c₀ / 4) / Real.log (|t| + 2) ≤ σ) (hσlo' : 1 - 1 / Real.log (|t| + 2) ≤ σ)
    (hσhi : σ ≤ 1 + 1 / Real.log (|t| + 2)) :
    ‖deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I)
        + 1 / (((σ : ℂ) + t * I) - 1)‖
      ≤ (1441 + 60 / c₀) * Real.log (|t| + 2) ^ 2 := by
  set T := |t|
  set L := Real.log (T + 2)
  have hLpos : 0 < L := by linarith
  have hT3 : 3 ≤ T := by linarith [Real.log_le_sub_one_of_pos (show 0 < T + 2 by linarith [abs_nonneg t])]
  set u := 1 / L
  have hu24 : u ≤ 1 / 24 := one_div_le_one_div_of_le (by norm_num) hL
  set σ₀ := 1 + u
  have hσ₀1 : 1 < σ₀ := by simp only [σ₀, u]; linarith [show 0 < 1 / L by positivity]
  have hσ₀2 : σ₀ ≤ 2 := by linarith
  have hσK : 2 / (σ₀ - 1) ≤ 20000 * (T + 2) := by
    rw [show 2 / (σ₀ - 1) = 2 * L by simp only [σ₀, u, add_sub_cancel_left, div_div_eq_mul_div, div_one]]
    linarith [Real.log_le_sub_one_of_pos (show 0 < T + 2 by linarith [abs_nonneg t])]
  set z₀ : ℂ := (σ₀ : ℂ) + t * I
  have hz0 : riemannZeta z₀ ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simpa [z₀] using hσ₀1)
  obtain ⟨Z, m, hZ, -, hsum, hder⟩ := hLL riemannZeta z₀ (1 / 2) ((T + 2) ^ 10) (by norm_num)
    (one_le_pow₀ (by linarith)) (zfo_diff_ball hT3) hz0 (zfo_M_bound hG hI hσ₀1 hσ₀2 hσK hT3 hT3 (by linarith))
  have hlogM : Real.log ((T + 2) ^ 10) = 10 * L := by rw [Real.log_pow]; push_cast; ring
  rw [hlogM] at hsum hder
  set s : ℂ := (σ : ℂ) + t * I
  have hs_mem : s ∈ closedBall z₀ (1 / 2 / 6) := by
    rw [mem_closedBall, dist_eq_norm, show s - z₀ = ((σ - σ₀ : ℝ) : ℂ) by simp only [s, z₀, Complex.ofReal_sub]; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]; linarith
  have hs1 : s ≠ 1 := fun h => by
    have := congrArg Complex.im h; simp [s] at this; simp only [T, this, abs_zero] at hT3; linarith
  have hs_ne : riemannZeta s ≠ 0 := hZ0 s hs1 (by
    simp only [s, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero,
      add_im, mul_im, zero_add]
    linarith [div_le_div_of_nonneg_right (show c₀ / 4 ≤ c₀ by linarith) hLpos.le])
  have hD := hder s hs_mem hs_ne
  set δ := (c₀ / 4) / L
  have hδ : 0 < δ := by positivity
  have hterm : ∀ ρ ∈ Z, ‖(m ρ : ℂ) / (s - ρ)‖ ≤ (m ρ : ℝ) / δ := fun ρ hρ => by
    obtain ⟨hρb, hρ0⟩ := (hZ ρ).1 hρ
    rw [mem_closedBall, dist_eq_norm] at hρb
    have him : |ρ.im - t| ≤ 1 / 6 := by
      have h1 : (ρ - z₀).im = ρ.im - t := by simp [z₀]
      rw [← h1]; exact (Complex.abs_im_le_norm _).trans (by linarith)
    have hρim : |ρ.im| ≤ T + 1 / 6 := by linarith [abs_sub_abs_le_abs_sub ρ.im t]
    have hρim' : T - 1 / 6 ≤ |ρ.im| := by linarith [abs_sub_abs_le_abs_sub t ρ.im, abs_sub_comm t ρ.im]
    have hρ1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_im, abs_zero] at hρim'; linarith
    have hre : ρ.re < 1 - c₀ / Real.log (|ρ.im| + 2) := lt_of_not_ge fun hc => hZ0 ρ hρ1 hc hρ0
    have hlogρ : Real.log (|ρ.im| + 2) ≤ 2 * L := by
      rw [show 2 * L = Real.log ((T + 2) ^ 2) by rw [Real.log_pow]; push_cast; ring]
      exact Real.log_le_log (by positivity) (by nlinarith)
    have h2 : 2 * δ ≤ c₀ / Real.log (|ρ.im| + 2) := by
      rw [show 2 * δ = c₀ / (2 * L) by simp only [δ]; field_simp; ring]
      exact div_le_div_of_nonneg_left hc₀.le (Real.log_pos (by linarith [abs_nonneg ρ.im])) hlogρ
    have hn : δ < ‖s - ρ‖ := (show δ < (s - ρ).re by simp [s]; linarith).trans_le (Complex.re_le_norm _)
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ hn.le
  have hSm : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ (60 / c₀) * L ^ 2 := by
    have h1 := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    rw [← Finset.sum_div, ← Nat.cast_sum] at h1
    have h3 : 10 * L / Real.log 2 ≤ 15 * L := (div_le_iff₀ (by linarith [Real.log_two_gt_d9])).mpr (by nlinarith [Real.log_two_gt_d9])
    have h4 := div_le_div_of_nonneg_right (hsum.trans h3) hδ.le
    rw [show 15 * L / δ = (60 / c₀) * L ^ 2 by simp only [δ]; field_simp; ring] at h4
    exact h1.trans h4
  have hinv : ‖1 / (s - 1)‖ ≤ 1 := ldr_inv_sub_one_le (by simpa [s] using show 1 ≤ T by linarith)
  have hsplit : deriv riemannZeta s / riemannZeta s + 1 / (s - 1) =
      (deriv riemannZeta s / riemannZeta s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ))
        + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) + 1 / (s - 1) := by ring
  rw [hsplit]
  have htot := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hD hSm)) hinv)
  nlinarith

end Formalism.ZF
