module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.SuperdiagSgnConj
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

open Classical Formalism.L2.SG.GGMirabolic PI.GGConvScalarW
open scoped ComplexConjugate

namespace PI.GGMatBoundW

variable {F : Type} [Field F] [Fintype F] {k : ℕ} (ψ₀ : AddChar F ℂ)

theorem psiNat_inv (u : GL (Fin k) F) : psiNat ψ₀ u⁻¹ = conj (psiNat ψ₀ u) := by
  unfold psiNat
  by_cases hu : IsUni k u
  · rw [ite_eq_left (isUni_inv hu), ite_eq_left hu,
      eq_inv_of_mul_eq_one_left (psiU_inv_mul ψ₀ hu), psiU, ← AddChar.map_neg_eq_inv,
      AddChar.map_neg_eq_conj]
  · rw [ite_eq_right fun h => hu (by simpa using isUni_inv h), ite_eq_right hu, map_zero]

theorem gam_inv (x : GL (Fin k) F) : gam ψ₀ x⁻¹ = conj (gam ψ₀ x) := by
  simp only [gam, map_mul, map_inv₀, map_natCast, map_sum, ← psiNat_inv, mul_inv_rev, inv_inv,
    mul_assoc]

theorem gamProd_inv {ι : Type} [Fintype ι] {Fq : ι → Type} [∀ v, Field (Fq v)]
    [∀ v, Fintype (Fq v)] (ψ : ∀ v, AddChar (Fq v) ℂ) (x : ∀ v, GL (Fin k) (Fq v)) :
    gamProd ψ x⁻¹ = conj (gamProd ψ x) := by
  simp only [gamProd, map_prod, Pi.inv_apply, gam_inv]

end PI.GGMatBoundW
