module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

@[expose] public section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.TracePair

variable {E : Type} [Field E] [NumberField E] {N : ℕ}

private lemma one_le_prod_re {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) {d : E}
    (hd : IsIntegral ℤ d) (hpos : ∀ τ : Ψ, 0 < τ.1 d) : 1 ≤ ∏ τ : Ψ, (τ.1 d).re := by
  rw [Finset.prod_coe_sort Ψ fun τ => (τ d).re]
  have hreal : ∀ τ ∈ Ψ, ((τ d).re : ℂ) = τ d := fun τ hτ =>
    Complex.ext (by simp) (by simpa using (Complex.pos_iff.1 (hpos ⟨τ, hτ⟩)).2)
  have hcompl : ∏ τ ∈ Ψ, τ d = ∏ τ ∈ Ψᶜ, τ d :=
    Finset.prod_equiv (star_involutive.toPerm _) (fun τ => (hΨ τ).trans Finset.mem_compl.symm)
      fun τ hτ => (Complex.conj_eq_iff_re.2 (hreal τ hτ)).symm
  set r := ∏ τ ∈ Ψ, (τ d).re
  have hP : ∏ τ ∈ Ψ, τ d = r :=
    (Finset.prod_congr rfl fun τ hτ => (hreal τ hτ).symm).trans (Complex.ofReal_prod _ _).symm
  have hall : ((Algebra.norm ℚ d : ℚ) : ℂ) = ∏ τ : E →+* ℂ, τ d := by
    rw [← eq_ratCast (algebraMap ℚ ℂ), Algebra.norm_eq_prod_embeddings ℚ ℂ]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ fun _ => rfl
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm ℚ hd)
  rw [← Finset.prod_mul_prod_compl Ψ, ← hcompl, hP, ← hm, eq_intCast] at hall
  have hmr : (m : ℝ) = r * r := by exact_mod_cast hall
  have hr : 0 < r := Finset.prod_pos fun τ hτ => (Complex.pos_iff.1 (hpos ⟨τ, hτ⟩)).1
  have hm0 : (0 : ℤ) < m := by exact_mod_cast (hmr ▸ mul_pos hr hr : (0 : ℝ) < m)
  nlinarith [show (1 : ℝ) ≤ m by exact_mod_cast hm0]

private lemma card_mul_prod_rpow_le_sum {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    (Fintype.card ι : ℝ) * (∏ i, x i) ^ (1 / (Fintype.card ι : ℝ)) ≤ ∑ i, x i := by
  rw [one_div, mul_comm, ← le_div_iff₀ (by positivity)]
  simpa using Real.geom_mean_le_arith_mean Finset.univ (fun _ => 1) x (by simp)
    (by simp [Fintype.card_pos]) fun i _ => hx i

open scoped MatrixOrder in
private lemma card_mul_rpow_det_le_trace (hN : 0 < N)
    {A Y : Matrix (Fin N) (Fin N) ℂ} (hA : A.PosDef) (hY : Y.PosDef) :
    (N : ℝ) * (A.det.re * Y.det.re) ^ (1 / (N : ℝ)) ≤ (A * Y).trace.re := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_mul_star_self.mp hY.posSemidef.nonneg
  rw [star_eq_conjTranspose] at hY ⊢
  have hC : C.det * Cᴴ.det ≠ 0 := det_mul C Cᴴ ▸ hY.det_pos.ne'
  have hP := hA.conjTranspose_mul_mul_same
    (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det C).2 (left_ne_zero_of_mul hC).isUnit))
  have hAim : A.det.im = 0 := (Complex.pos_iff.1 hA.det_pos).2.symm
  have hYim : (C * Cᴴ).det.im = 0 := (Complex.pos_iff.1 hY.det_pos).2.symm
  have hdet : (Cᴴ * A * C).det = A.det * (C * Cᴴ).det := by
    simp only [det_mul]
    ring
  have hre : (Cᴴ * A * C).det.re = A.det.re * (C * Cᴴ).det.re := by
    rw [hdet, Complex.mul_re, hAim, hYim, mul_zero, sub_zero]
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [← Matrix.mul_assoc, trace_mul_cycle, ← hre, hP.isHermitian.det_eq_prod_eigenvalues,
    hP.isHermitian.trace_eq_sum_eigenvalues]
  simpa [← Complex.ofReal_prod, ← Complex.ofReal_sum] using
    card_mul_prod_rpow_le_sum hP.isHermitian.eigenvalues fun i => (hP.eigenvalues_pos i).le

theorem trace_ge :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)),
      IsType Ψ → ∀ N c : ℕ, 0 < N → 0 < c → ∃ k : ℝ, 0 < k ∧
        ∀ T : Matrix (Fin N) (Fin N) E, ccT T = T → Den c T → (∀ τ : Ψ, (T.map τ.1).PosDef) →
          ∀ Z ∈ Hn Ψ N, k * detIm Z ^ (1 / ((Ψ.card * N : ℕ) : ℝ)) ≤
            ∑ τ : Ψ, (T.map τ.1 * imH (Z τ)).trace.re := by
  intro E _ _ _ Ψ hΨ N c hN hc
  have hne : Ψ.Nonempty := Finset.nonempty_iff_ne_empty.2 fun h => by
    simpa [h] using hΨ (Classical.arbitrary _)
  have : Nonempty Ψ := hne.to_subtype
  refine ⟨(Ψ.card * N : ℝ) / c, by positivity, fun T _ hden hpos Z hZ => ?_⟩
  have hY : ∀ τ : Ψ, (imH (Z τ)).PosDef := by simpa [Hn] using hZ
  have hA : ∀ τ : Ψ, ((c : ℂ) • T.map τ.1).PosDef := fun τ => (hpos τ).smul (by exact_mod_cast hc)
  have hdet : ∀ τ : E →+* ℂ, τ ((c : E) • T).det = ((c : ℂ) • T.map τ).det := fun τ => by
    rw [RingHom.map_det]; congr 1; ext; simp
  set a : Ψ → ℝ := fun τ => ((c : ℂ) • T.map τ.1).det.re
  set y : Ψ → ℝ := fun τ => (imH (Z τ)).det.re
  have ha : ∀ τ, 0 < a τ := fun τ => (Complex.pos_iff.1 (hA τ).det_pos).1
  have hy : ∀ τ, 0 < y τ := fun τ => (Complex.pos_iff.1 (hY τ).det_pos).1
  have hay : ∀ τ ∈ Finset.univ, 0 ≤ a τ * y τ := fun τ _ => (mul_pos (ha τ) (hy τ)).le
  have hDnn : 0 ≤ detIm Z := Finset.prod_nonneg fun τ _ => (hy τ).le
  have hprod_a : 1 ≤ ∏ τ, a τ := by
    simpa only [hdet] using
      one_le_prod_re hΨ (IsIntegral.det hden) fun τ => hdet τ ▸ (hA τ).det_pos
  have key : detIm Z ^ (1 / ((Ψ.card * N : ℕ) : ℝ)) ≤
      (∏ τ, (a τ * y τ) ^ (1 / (N : ℝ))) ^ (1 / (Ψ.card : ℝ)) := by
    rw [Real.finsetProd_rpow _ _ hay, ← Real.rpow_mul (Finset.prod_nonneg hay),
      Finset.prod_mul_distrib, one_div_mul_one_div, Nat.cast_mul, mul_comm (Ψ.card : ℝ)]
    exact Real.rpow_le_rpow hDnn (le_mul_of_one_le_left hDnn hprod_a) (by positivity)
  have hamgm := card_mul_prod_rpow_le_sum (fun τ : Ψ => (a τ * y τ) ^ (1 / (N : ℝ)))
    fun τ => Real.rpow_nonneg (hay τ (Finset.mem_univ _)) _
  rw [Fintype.card_coe] at hamgm
  rw [div_mul_eq_mul_div, div_le_iff₀' (by positivity)]
  calc (Ψ.card * N : ℝ) * detIm Z ^ (1 / ((Ψ.card * N : ℕ) : ℝ))
      ≤ N * (Ψ.card * (∏ τ, (a τ * y τ) ^ (1 / (N : ℝ))) ^ (1 / (Ψ.card : ℝ))) := by
        rw [mul_comm (Ψ.card : ℝ), mul_assoc]; gcongr
    _ ≤ N * ∑ τ, (a τ * y τ) ^ (1 / (N : ℝ)) := by gcongr
    _ ≤ c * ∑ τ, (T.map τ.1 * imH (Z τ)).trace.re := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_le_sum fun τ _ => ?_
        exact (card_mul_rpow_det_le_trace hN (hA τ) (hY τ)).trans_eq (by simp [trace_smul])

end GlobalTheory.SW.TracePair
