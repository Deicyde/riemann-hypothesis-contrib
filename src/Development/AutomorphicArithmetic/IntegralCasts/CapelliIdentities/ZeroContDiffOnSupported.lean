module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace UpperTheory.Reformulated.B.H23

noncomputable section

@[reducible] def Pl (E : Type) [Field E] [NumberField E] : Type :=
  IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)

@[reducible] def GLw {E : Type} [Field E] [NumberField E] (n : ℕ) (w : Pl E) : Type :=
  Matrix.GeneralLinearGroup (Fin n) (w.adicCompletion E)

theorem aux3 (k : Type) [Field k] : SubsemiringClass (Subring k) k :=
  inferInstance

theorem aux4 (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] :
    IsLocalRing (ValuativeRel.valuation k).integer :=
  inferInstance

def blk {α n : Type} {m : α → Type} (e : (a : α) × m a ≃ n) (i : n) : α :=
  (e.symm i).fst

theorem aux6 (R : Type) [CommRing R] {α n : Type} {m : α → Type}
    [LinearOrder α] [Fintype n] [DecidableEq n] (e : (a : α) × m a ≃ n)
    {x y : Matrix.GeneralLinearGroup n R}
    (hx : x ∈ {g : Matrix.GeneralLinearGroup n R | g.val.BlockTriangular (blk e)})
    (hy : y ∈ {g : Matrix.GeneralLinearGroup n R | g.val.BlockTriangular (blk e)}) :
    x * y ∈ {g : Matrix.GeneralLinearGroup n R | g.val.BlockTriangular (blk e)} :=
  Matrix.BlockTriangular.mul hx hy

theorem aux7 (R : Type) [CommRing R] {α n : Type} {m : α → Type}
    [LinearOrder α] [Fintype n] [DecidableEq n] (e : (a : α) × m a ≃ n) :
    (1 : Matrix.GeneralLinearGroup n R) ∈
      {g : Matrix.GeneralLinearGroup n R | g.val.BlockTriangular (blk e)} :=
  Matrix.blockTriangular_one

theorem aux8 (R : Type) [CommRing R] {α n : Type} {m : α → Type}
    [LinearOrder α] [Fintype n] [DecidableEq n] (e : (a : α) × m a ≃ n)
    {x : Matrix.GeneralLinearGroup n R}
    (hx : x ∈ {g : Matrix.GeneralLinearGroup n R | g.val.BlockTriangular (blk e)}) :
    x⁻¹ ∈ {g : Matrix.GeneralLinearGroup n R | g.val.BlockTriangular (blk e)} := by
  change Matrix.BlockTriangular (x⁻¹ : Matrix.GeneralLinearGroup n R).val _
  rw [Matrix.coe_units_inv]
  let := x.invertible
  exact Matrix.blockTriangular_inv_of_blockTriangular hx

def parab (R : Type) [CommRing R] {α n : Type} {m : α → Type}
    [LinearOrder α] [Fintype n] [DecidableEq n] (e : (a : α) × m a ≃ n) :
    Subgroup (Matrix.GeneralLinearGroup n R) where
  carrier := {g : Matrix.GeneralLinearGroup n R | g.val.BlockTriangular (blk e)}
  mul_mem' := aux6 R e
  one_mem' := aux7 R e
  inv_mem' := aux8 R e

def points (n : Type) : (_ : n) × Unit ≃ n :=
  Equiv.sigmaUnique n (fun _ => Unit)

def borel (R : Type) [CommRing R] (n : Type)
    [Fintype n] [DecidableEq n] [LinearOrder n] :
    Subgroup (Matrix.GeneralLinearGroup n R) :=
  parab R (points n)

def iwahori (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] :
    Subgroup (Matrix.GeneralLinearGroup n k) :=
  Subgroup.map
    (Matrix.GeneralLinearGroup.map (algebraMap (ValuativeRel.valuation k).integer k))
    (Subgroup.comap
      (Matrix.GeneralLinearGroup.map (IsLocalRing.residue (ValuativeRel.valuation k).integer))
      (borel (IsLocalRing.ResidueField (ValuativeRel.valuation k).integer) n))

@[reducible] def complRel {F : Type} [Field F] [NumberField F]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ValuativeRel (p.adicCompletion F) :=
  ValuativeRel.ofValuation
    (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ)))

open IsDedekindDomain NumberField in
private theorem exists_global_approx {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (RingOfIntegers F)) (x : p.adicCompletion F)
    (hx : Valued.v x ≤ 1) :
    ∃ r : RingOfIntegers F,
      Valued.v (algebraMap F (p.adicCompletion F) (algebraMap (RingOfIntegers F) F r) - x) < 1 := by
  have hval : ∀ k : F, Valued.v (algebraMap F (p.adicCompletion F) k) = p.valuation F k :=
    fun k ↦ p.valuedAdicCompletion_eq_valuation' k
  have hn : {y : p.adicCompletion F | Valued.v (y - x) < 1} ∈ nhds x := by
    rw [Valued.mem_nhds]
    refine ⟨1, fun y hy ↦ ?_⟩
    exact (Valuation.restrict_lt_one_iff _).mp hy
  obtain ⟨k, hk⟩ := (p.denseRange_algebraMap F).mem_nhds hn
  have hk' : Valued.v (algebraMap F (p.adicCompletion F) k - x) < 1 := hk
  have hk1 : p.valuation F k ≤ 1 := by
    rw [← hval, ← sub_add_cancel (algebraMap F (p.adicCompletion F) k) x]
    exact Valuation.map_add_le _ hk'.le hx
  obtain ⟨r, hr⟩ := p.exists_valuation_sub_lt_of_integer hk1 1
  refine ⟨r, ?_⟩
  rw [← sub_add_sub_cancel _ (algebraMap F (p.adicCompletion F) k) x]
  refine Valuation.map_add_lt _ ?_ hk'
  rw [← map_sub, hval]
  exact hr

open IsDedekindDomain NumberField in
private theorem finite_residueField {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (RingOfIntegers F)) :
    Finite (IsLocalRing.ResidueField (p.adicCompletionIntegers F)) := by
  have hval : ∀ k : F, Valued.v (algebraMap F (p.adicCompletion F) k) = p.valuation F k :=
    fun k ↦ p.valuedAdicCompletion_eq_valuation' k
  have hmem : ∀ y : p.adicCompletionIntegers F, Valued.v (y : p.adicCompletion F) < 1 →
      IsLocalRing.residue (p.adicCompletionIntegers F) y = 0 := by
    intro y hy
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact hy.ne
  let f : RingOfIntegers F →+* IsLocalRing.ResidueField (p.adicCompletionIntegers F) :=
    (IsLocalRing.residue _).comp (algebraMap (RingOfIntegers F) (p.adicCompletionIntegers F))
  have hker : ∀ a ∈ p.asIdeal, f a = 0 := by
    intro a ha
    refine hmem _ ?_
    have h := (p.valuation_lt_one_iff_mem (K := F) a).mpr ha
    rw [← hval] at h
    exact h
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨r, hr⟩ := exists_global_approx p x.1 x.2
    refine ⟨r, ?_⟩
    rw [← sub_eq_zero]
    have h := hmem (algebraMap (RingOfIntegers F) (p.adicCompletionIntegers F) r - x) hr
    rw [map_sub] at h
    exact h
  have : Finite (RingOfIntegers F ⧸ p.asIdeal) := p.asIdeal.finiteQuotientOfFreeOfNeBot p.ne_bot
  exact Finite.of_surjective (Ideal.Quotient.lift p.asIdeal f hker)
    (Ideal.Quotient.lift_surjective_of_surjective _ hker hsurj)

open IsDedekindDomain NumberField in
private theorem locallyCompact {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (RingOfIntegers F)) :
    LocallyCompactSpace (p.adicCompletion F) := by
  have hc : CompactSpace (Valued.integer (p.adicCompletion F)) := by
    rw [Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]
    refine ⟨(Valued.isClosed_integer (p.adicCompletion F)).completeSpace_coe,
      inferInstanceAs (IsDiscreteValuationRing (p.adicCompletionIntegers F)),
      finite_residueField p⟩
  have hc' : IsCompact (Valued.integer (p.adicCompletion F) : Set (p.adicCompletion F)) :=
    isCompact_iff_compactSpace.mpr hc
  exact hc'.locallyCompactSpace_of_mem_nhds_of_addGroup (x := 0)
    ((Valued.isOpen_integer (p.adicCompletion F)).mem_nhds (zero_mem _))

section
attribute [local instance high] complRel

theorem zero_contDiffOn_supported {F : Type} [Field F] [NumberField F]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    IsNonarchimedeanLocalField (p.adicCompletion F) := by
  have : (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact
    { toIsValuativeTopology :=
        IsValuativeTopology.of_mem_nhds_iff_vle
          (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ))) Valued.mem_nhds
      toLocallyCompactSpace := locallyCompact p
      toIsNontrivial :=
        (ValuativeRel.isNontrivial_iff_isNontrivial
          (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ)))).mpr
          inferInstance }

attribute [local instance high] zero_contDiffOn_supported

def iwGL {E : Type} [Field E] [NumberField E] (n : ℕ) (w : Pl E) :
    Subgroup (GLw n w) :=
  iwahori (w.adicCompletion E) (Fin n)

end

open scoped Classical in
def dcos {E : Type} [Field E] [NumberField E] (n : ℕ) (w : Pl E)
    (t y : GLw n w) : ℂ :=
  if ∃ x ∈ iwGL n w, ∃ z ∈ iwGL n w, y = x * t * z then 1 else 0

theorem dcos_right {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {m : ℕ} {w : Pl E} (t k g : GLw m w) (hk : k ∈ iwGL m w) :
    dcos m w t (g * k) = dcos m w t g := by
  classical
  unfold dcos
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨x, hx, z, hz, h⟩
    exact ⟨x, hx, z * k⁻¹, Subgroup.mul_mem _ hz (Subgroup.inv_mem _ hk), by
      rw [← mul_assoc, ← h, mul_inv_cancel_right]⟩
  · rintro ⟨x, hx, z, hz, h⟩
    exact ⟨x, hx, z * k, Subgroup.mul_mem _ hz hk, by rw [h, mul_assoc (x * t)]⟩

end

end UpperTheory.Reformulated.B.H23
