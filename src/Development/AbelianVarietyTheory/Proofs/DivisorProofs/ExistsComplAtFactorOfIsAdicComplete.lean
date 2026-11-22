module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Polynomial
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
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem exists_complAt_factor_of_isAdicComplete : ∀ (W : Type) [CommRing W] [IsRegularLocalRing W] (I : Type) [Fintype I] (V : Type) [CommRing V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → ∀ ψV : MvPolynomial I W →+* V, IsLocalHom (ψV.comp MvPolynomial.C) → ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (ψ : MvPolynomial I W →+* R) (θ : R →+* V), IsComplAt ψ ∧ IsLocalHom θ ∧ θ.comp ψ = ψV ∧ IsLocalHom (ψ.comp MvPolynomial.C) := by
  intro W _ _ I _ V _ _ hV ψV hC
  haveI := hV
  let A := MvPolynomial I W
  let q : Ideal A := (maximalIdeal V).comap ψV
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  let L := Localization.AtPrime q
  haveI : IsRegularRing W := GlobalTheory.isRegularRing_of_isRegularLocalRing W
  haveI : IsRegularLocalRing L := inferInstance
  let R := AdicCompletion (maximalIdeal L) L
  haveI : IsRegularLocalRing R := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion L
  haveI : IsDomain R := inferInstance
  haveI : IsNoetherianRing R := inferInstance
  have hfg : (maximalIdeal L).FG := (maximalIdeal L).fg_of_isNoetherianRing
  have hunit : ∀ y : q.primeCompl, IsUnit (ψV y) := fun y => by
    have := y.2
    exact IsLocalRing.notMem_maximalIdeal.mp this
  let φ : L →+* V := IsLocalization.lift (M := q.primeCompl) (S := L) hunit
  have hφ : φ.comp (algebraMap A L) = ψV := IsLocalization.lift_comp hunit
  have hmL : (maximalIdeal L) = q.map (algebraMap A L) := (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hk : (maximalIdeal L).map φ ^ 1 ≤ maximalIdeal V := by
    rw [pow_one, hmL, Ideal.map_map, hφ]
    exact Ideal.map_comap_le
  obtain ⟨θ, hθ, -⟩ := GlobalTheory.exists_extend_adicCompletion φ (maximalIdeal L) (maximalIdeal V) hk
  let c : L →+* R := algebraMap L R
  let ψ : A →+* R := c.comp (algebraMap A L)
  have hθψ : θ.comp ψ = ψV := by
    show θ.comp (c.comp (algebraMap A L)) = ψV
    rw [← RingHom.comp_assoc]
    show (θ.comp (algebraMap L R)).comp (algebraMap A L) = ψV
    rw [hθ, hφ]
  have hmR : maximalIdeal R = q.map ψ := by
    have h0 := AdicCompletion.maximalIdeal_eq_map (R := L)
    have hmL' : q.map (algebraMap A L) = maximalIdeal L := Localization.AtPrime.map_eq_maximalIdeal
    rw [h0]
    show _ = q.map (c.comp (algebraMap A L))
    rw [← Ideal.map_map, hmL']
  refine ⟨R, inferInstance, inferInstance, inferInstance, ψ, θ, ⟨inferInstance, inferInstance, ?_, ?_, ?_⟩, ?_, hθψ, ?_⟩
  · exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat L q.primeCompl))
      (RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _))
  · apply le_antisymm Ideal.map_comap_le
    have : q ≤ (maximalIdeal R).comap ψ := by
      rw [← Ideal.map_le_iff_le_comap, ← hmR]
    rw [hmR]
    exact Ideal.map_mono (hmR ▸ this)
  · intro r
    obtain ⟨x, hx⟩ := (AdicCompletion.residueField_map_bijective_of_fg (R := L) hfg).2 (residue R r)
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl y
    refine ⟨a, s, ?_, ?_⟩
    · exact (IsLocalization.map_units L s).map c
    · have h1 : residue R (c (IsLocalization.mk' L a s)) = residue R r := by
        rw [← hx, ResidueField.map_residue]
      have h2 : r - c (IsLocalization.mk' L a s) ∈ maximalIdeal R := by
        rw [← residue_eq_zero_iff, (residue R).map_sub, h1, sub_self]
      have h3 : c (IsLocalization.mk' L a s) * ψ s = ψ a := by
        show c (IsLocalization.mk' L a s) * c (algebraMap A L s) = c (algebraMap A L a)
        rw [← map_mul, IsLocalization.mk'_spec]
      have : r * ψ s - ψ a = (r - c (IsLocalization.mk' L a s)) * ψ s := by
        rw [sub_mul, h3]
      rw [this]
      exact Ideal.mul_mem_right _ _ h2
  · haveI : IsLocalHom (θ.comp (algebraMap L R)) := by
      rw [hθ]
      apply ((IsLocalRing.local_hom_tfae φ).out 1 3).mpr
      simpa using hk
    exact GlobalTheory.isLocalHom_of_extend_adicCompletion hfg θ
  · refine ⟨fun a ha => hC.map_nonunit a ?_⟩
    have : θ ((ψ.comp MvPolynomial.C) a) = (ψV.comp MvPolynomial.C) a := by
      simp only [RingHom.comp_apply]
      exact congrArg (fun f : A →+* V => f (MvPolynomial.C a)) hθψ
    rw [← this]
    exact ha.map θ

end GlobalTheory.TChart
