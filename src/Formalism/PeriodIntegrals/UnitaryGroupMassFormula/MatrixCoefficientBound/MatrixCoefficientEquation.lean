module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.PermRepApply
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.GammaMatrixInverse

@[expose] public section

open Matrix Classical Formalism.L2.SG.GGMirabolic

namespace PI.GGMatBoundW

theorem sum_orbit {G X : Type} [Group G] [Fintype G] [MulAction Gᵐᵒᵖ X]
    (hfree : ∀ (x : Gᵐᵒᵖ) (j : X), x • j = j → x = 1) (d : X → X → G)
    (hd : ∀ i j, (∃ x : Gᵐᵒᵖ, x • j = i) → MulOpposite.op (d i j) • j = i) (f : G → ℂ) (i j : X) :
    (∑ x : G, if MulOpposite.op x • j = i then f x else 0) =
      if ∃ x : Gᵐᵒᵖ, x • j = i then f (d i j) else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (d i j), ite_eq_left (hd i j h)]
    · refine fun b _ hb => ite_eq_right fun hbj => hb (MulOpposite.op_injective ?_).symm
      refine inv_mul_eq_one.1 (hfree _ j ?_)
      rw [mul_smul, inv_smul_eq_iff, hbj, hd i j h]
    · simp
  · exact Finset.sum_eq_zero fun x _ => ite_eq_right fun hx => h ⟨_, hx⟩

theorem toMatrix'_totOp_apply {ι : Type} [Fintype ι] {Fq : ι → Type} [∀ v, Field (Fq v)]
    [∀ v, Fintype (Fq v)] {k : ℕ} (ψ : ∀ v, AddChar (Fq v) ℂ) (X : Type) [Fintype X]
    [MulAction (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ X] (i j : X) :
    LinearMap.toMatrix' (totOp ψ (permRep (∀ v, GL (Fin k) (Fq v)) X)) i j =
      ∑ x : (∀ v, GL (Fin k) (Fq v)), if MulOpposite.op x • i = j then gamProd ψ x else 0 := by
  rw [LinearMap.toMatrix'_apply]
  simp [totOp, permRep, LinearMap.funLeft, Finset.sum_apply, Pi.single_apply, mul_ite]

theorem totally_hermitian_form : TotHerm := by
  intro ι _ Fq _ _ k ψ X _ _
  refine IsHermitian.ext fun i j => ?_
  rw [toMatrix'_totOp_apply, toMatrix'_totOp_apply, star_sum]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun x => ?_
  have hiff : MulOpposite.op x • j = i ↔ MulOpposite.op x⁻¹ • i = j := by
    rw [MulOpposite.op_inv, inv_smul_eq_iff, eq_comm]
  simp only [hiff, Equiv.inv_apply, gamProd_inv]
  split_ifs <;> simp

theorem matrix_coefficient_equation : MatrixEq := by
  intro ι _ Fq _ _ k ψ X _ _ hfree d hd
  have hT : (of fun i j => if ∃ x : (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ, x • j = i then gamProd ψ (d i j)
      else 0) = (LinearMap.toMatrix' (totOp ψ (permRep (∀ v, GL (Fin k) (Fq v)) X)))ᵀ := by
    ext i j
    rw [of_apply, transpose_apply, toMatrix'_totOp_apply, sum_orbit hfree d hd]
  refine ⟨?_, hT⟩
  ext i j
  have h := congrFun (congrFun hT i) j
  rw [of_apply, transpose_apply] at h
  rw [of_apply, ← (totally_hermitian_form ι Fq k ψ X).apply i j, ← h]
  split_ifs <;> simp

end PI.GGMatBoundW
