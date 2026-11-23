module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
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
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Complex Filter Topology

noncomputable section

namespace Formalism.ZF

lemma rso_zeta_ne_near_one : ∀ᶠ w in 𝓝 (1 : ℂ), w ≠ 1 → riemannZeta w ≠ 0 := by
  filter_upwards [eventually_nhdsWithin_iff.mp (riemannZeta_residue_one.eventually_ne one_ne_zero)]
    with w hw hw1 hz using hw hw1 (by rw [hz, mul_zero])

lemma rso_deriv_zeta_diff : DifferentiableOn ℂ (deriv riemannZeta) {w : ℂ | w ≠ 1} :=
  DifferentiableOn.deriv (fun _ hw => (differentiableAt_riemannZeta hw).differentiableWithinAt) isOpen_ne

lemma rso_Fy_diff (y : ℝ) (hy : 0 < y) {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1)
    (hz : riemannZeta w ≠ 0) : DifferentiableAt ℂ (Fy y) w := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  exact (((rso_deriv_zeta_diff.differentiableAt (isOpen_ne.mem_nhds h1)).div
    (differentiableAt_riemannZeta h1) hz).neg.mul (differentiableAt_id.const_cpow (Or.inl hy0))).div
    (differentiableAt_id.mul (differentiableAt_id.sub_const 1)) (mul_ne_zero h0 (sub_ne_zero.2 h1))

theorem rectangleShiftOfResidue : RectShiftOf := by
  intro hRDP hLA y hy σ₁ σ₀ T h1 h2 h3 hT hz
  obtain ⟨A, hA1, hAev⟩ := hLA y hy
  set a : ℂ := (y : ℂ)
  set b : ℂ := (y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y
  let H : ℂ → ℂ := fun w => Fy y w - a / (w - 1) ^ 2 - b / (w - 1)
  let G : ℂ → ℂ := fun w => if w = 1 then A 1 else H w
  have hG : ∀ z : ℂ, z ≠ 0 → z ≠ 1 → riemannZeta z ≠ 0 → DifferentiableAt ℂ G z := fun z hz0 hz1 hzz => by
    have hzm : z - 1 ≠ 0 := sub_ne_zero.2 hz1
    have hH : DifferentiableAt ℂ H z := ((rso_Fy_diff y hy hz0 hz1 hzz).sub
      ((differentiableAt_const a).div ((differentiableAt_id.sub_const 1).pow 2) (pow_ne_zero 2 hzm))).sub
      ((differentiableAt_const b).div (differentiableAt_id.sub_const 1) hzm)
    exact hH.congr_of_eventuallyEq (by filter_upwards [isOpen_ne.mem_nhds hz1] with w hw; simp [G, hw])
  have hG1 : DifferentiableAt ℂ G 1 := hA1.congr_of_eventuallyEq <| by
    filter_upwards [eventually_nhdsWithin_iff.mp hAev] with w hw
    by_cases hw1 : w = 1
    · subst hw1; simp [G]
    · simp only [G, H, if_neg hw1]; rw [hw hw1]; ring
  set U : Set ℂ := {w | ∀ᶠ z in 𝓝 w, DifferentiableAt ℂ G z}
  have hsub : (Set.uIcc σ₁ σ₀ ×ℂ Set.uIcc (-T) T) ⊆ U := fun w hw => by
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hw
    obtain ⟨⟨hr1, hr2⟩, hi1, hi2⟩ := hw
    have hw0 : w ≠ 0 := fun h => by rw [h] at hr1; simp at hr1; linarith
    by_cases hw1 : w = 1
    · subst hw1
      filter_upwards [rso_zeta_ne_near_one, eventually_ne_nhds one_ne_zero] with z hz1 hz0
      by_cases hz1' : z = 1
      · subst hz1'; exact hG1
      · exact hG z hz0 hz1' (hz1 hz1')
    · filter_upwards [(differentiableAt_riemannZeta hw1).continuousAt.eventually_ne
        (hz w hr1 hr2 (abs_le.2 ⟨hi1, hi2⟩) hw1), isOpen_ne.mem_nhds hw1, isOpen_ne.mem_nhds hw0]
        with z hzz hz1 hz0 using hG z hz0 hz1 hzz
  refine hRDP (Fy y) G a b 1 σ₁ σ₀ (-T) T (by simpa using h2) (by simpa using h3)
    (by simp; linarith) (by simpa using hT)
    ⟨U, isOpen_setOfPred_eventually_nhds, hsub, fun _ hw => hw.self_of_nhds.differentiableWithinAt⟩
    fun w hw => by simp only [G, H, if_neg hw]; ring

end Formalism.ZF
