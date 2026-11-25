module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Different
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain
open Classical

namespace GlobalTheory.InvDiffLocal


open IsDedekindDomain.HeightOneSpectrum in
theorem exists_not_mem_mul_mem {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (t : K)
    (ht : v.valuation K t ≤ 1) :
    ∃ s : R, s ∉ v.asIdeal ∧ ∃ r : R, algebraMap R K s * t = algebraMap R K r := by
  obtain ⟨r, s, h⟩ := exists_primeCompl_mul_eq_of_integer v t ht
  exact ⟨s, s.2, r, by rw [mul_comm, h]⟩

end GlobalTheory.InvDiffLocal

namespace GlobalTheory.InvDiffLocal

theorem mul_mem_of_trace_mem {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (x : L)
    (hx : ∀ b : 𝓞 L, Algebra.trace K L ((b : L) * x) ∈ (algebraMap (𝓞 K) K).range) :
    ∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), ∃ c : 𝓞 L, (c : L) = x * (d : L) := by
  intro d hd
  have hxd : x ∈ FractionalIdeal.dual (𝓞 K) K (1 : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) := by
    rw [FractionalIdeal.mem_dual (by simp)]
    intro a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply, mul_comm]
    exact hx b
  have hdd : (d : L) ∈ ((differentIdeal (𝓞 K) (𝓞 L) : Ideal (𝓞 L)) : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩
  rw [coeIdeal_differentIdeal (𝓞 K) K] at hdd
  have hm := FractionalIdeal.mul_mem_mul hxd hdd
  rw [mul_inv_cancel₀ (FractionalIdeal.dual_ne_zero (𝓞 K) K (by simp))] at hm
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hm
  exact ⟨c, hc⟩

end GlobalTheory.InvDiffLocal

namespace GlobalTheory.InvDiffLocal


open IsDedekindDomain.HeightOneSpectrum in
theorem exists_approx_idempotent {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (la : HeightOneSpectrum (𝓞 L)) (p : HeightOneSpectrum (𝓞 K)) (N : ℕ) :
    ∃ z : 𝓞 L, z ∉ la.asIdeal ∧ ∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la →
      la'.asIdeal.under (𝓞 K) = p.asIdeal → z ∈ la'.asIdeal ^ N := by
  set S : Set (HeightOneSpectrum (𝓞 L)) := {la' | la' ≠ la ∧ la'.asIdeal.under (𝓞 K) = p.asIdeal}
  haveI := p.isMaximal
  have hfin : S.Finite := by
    refine ((IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 L)).preimage
      (f := HeightOneSpectrum.asIdeal) ?_).subset ?_
    · intro a _ b _ h; exact HeightOneSpectrum.ext h
    · intro la' h
      exact ⟨la'.isPrime, ⟨h.2.symm⟩⟩
  haveI := la.isPrime
  have hw : ∀ la' ∈ S, ∃ w : 𝓞 L, w ∈ la'.asIdeal ^ N ∧ w ∉ la.asIdeal := by
    intro la' h
    by_contra! hc
    have h1 : la'.asIdeal ^ N ≤ la.asIdeal := fun w hw => hc w hw
    have h2 := Ideal.IsPrime.le_of_pow_le h1
    exact h.1 (HeightOneSpectrum.ext (la'.isMaximal.eq_of_le la.isPrime.ne_top h2))
  choose! w hwN hwla using hw
  refine ⟨∏ la' ∈ hfin.toFinset, w la', ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨i, hi, hmem⟩
    exact hwla i (hfin.mem_toFinset.1 hi) hmem
  · intro la' h1 h2
    have hS : la' ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨h1, h2⟩
    rw [← Finset.mul_prod_erase _ _ hS]
    exact Ideal.mul_mem_right _ _ (hwN la' ⟨h1, h2⟩)

end GlobalTheory.InvDiffLocal

namespace GlobalTheory.InvDiffLocal


open IsDedekindDomain.HeightOneSpectrum in
theorem valuation_mul_different_le_one : ∀ (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (la : HeightOneSpectrum (𝓞 L)) (p : HeightOneSpectrum (𝓞 K)),
    la.asIdeal.under (𝓞 K) = p.asIdeal → ∀ y : L, (∃ N : ℕ, ∀ b : 𝓞 L,
      (∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la → la'.asIdeal.under (𝓞 K) = p.asIdeal →
        b ∈ la'.asIdeal ^ N) → p.valuation K (Algebra.trace K L ((b : L) * y)) ≤ 1) →
    ∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), la.valuation L (y * (d : L)) ≤ 1 := by
  intro K L _ _ _ _ _ la p hp y ⟨N, hN⟩ d hd
  obtain ⟨z, hzla, hzN⟩ := exists_approx_idempotent (K := K) la p N
  set x : L := (z : L) * y with hxdef
  have hx : ∀ b : 𝓞 L, p.valuation K (Algebra.trace K L ((b : L) * x)) ≤ 1 := by
    intro b
    have h := hN (b * z) (fun la' h1 h2 => Ideal.mul_mem_left _ _ (hzN la' h1 h2))
    rw [hxdef, ← mul_assoc]
    simpa using h
  set bs := RingOfIntegers.basis L
  have hloc : ∀ i, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ ∃ r : 𝓞 K,
      algebraMap (𝓞 K) K s * Algebra.trace K L ((bs i : L) * x) = algebraMap (𝓞 K) K r :=
    fun i => exists_not_mem_mul_mem p _ (hx (bs i))
  choose s hsp r hr using hloc
  set s0 : 𝓞 K := ∏ i, s i with hs0
  haveI := p.isPrime
  have hs0p : s0 ∉ p.asIdeal := by
    rw [hs0, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨i, _, hi⟩
    exact hsp i hi
  have hgen : ∀ b : 𝓞 L,
      algebraMap (𝓞 K) K s0 * Algebra.trace K L ((b : L) * x) ∈ (algebraMap (𝓞 K) K).range := by
    intro b
    have hb : b ∈ Submodule.span ℤ (Set.range bs) := by rw [bs.span_eq]; trivial
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨i, rfl⟩ := hb
      rw [hs0, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul, mul_comm (algebraMap _ _ (s i)),
        mul_assoc, hr i, ← map_mul]
      exact ⟨_, rfl⟩
    | zero => simp
    | add b c _ _ hb hc =>
      have : ((b + c : 𝓞 L) : L) * x = (b : L) * x + (c : L) * x := by push_cast; ring
      rw [this, map_add (f := _), mul_add]
      exact add_mem hb hc
    | smul n b _ hb =>
      have : ((n • b : 𝓞 L) : L) * x = n • ((b : L) * x) := by
        rw [← smul_mul_assoc]; congr 1
      rw [this, map_zsmul, mul_smul_comm]
      exact zsmul_mem hb n
  set x' : L := algebraMap (𝓞 K) L s0 * x with hx'def
  have htr : ∀ b : 𝓞 L, Algebra.trace K L ((b : L) * x') ∈ (algebraMap (𝓞 K) K).range := by
    intro b
    have : (b : L) * x' = (algebraMap (𝓞 K) K s0) • ((b : L) * x) := by
      rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, hx'def]; ring
    rw [this, map_smul, smul_eq_mul]
    exact hgen b
  obtain ⟨c, hc⟩ := mul_mem_of_trace_mem x' htr d hd
  have hcle : la.valuation L (c : L) ≤ 1 := la.valuation_le_one c
  have hs0la : la.valuation L (algebraMap (𝓞 K) L s0) = 1 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L]
    refine le_antisymm (la.valuation_le_one _) (not_lt.1 fun h => hs0p ?_)
    rw [la.valuation_lt_one_iff_mem] at h
    rw [← hp]
    exact h
  have hzla' : la.valuation L (z : L) = 1 := by
    refine le_antisymm (la.valuation_le_one z) (not_lt.1 fun h => hzla ?_)
    exact (la.valuation_lt_one_iff_mem z).1 h
  have : (c : L) = (algebraMap (𝓞 K) L s0 * (z : L)) * (y * (d : L)) := by
    rw [hc, hx'def, hxdef]; ring
  rw [this, map_mul, map_mul, hs0la, hzla', one_mul, one_mul] at hcle
  exact hcle

end GlobalTheory.InvDiffLocal
