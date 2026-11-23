module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.PermRepApply
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.SuperdiagSgnConj

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
