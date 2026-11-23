module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.PermRepApply

@[expose] public section

open Classical Formalism.L2.SG.GGMirabolic

namespace PI.GGMatBoundW

variable {ι : Type} [Fintype ι] {Fq : ι → Type} [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] {k : ℕ}
  (ψ : ∀ v, AddChar (Fq v) ℂ) {V : Type} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V)

noncomputable def beta (s : Finset ι) (x : ∀ v, GL (Fin k) (Fq v)) : ℂ :=
  if ∀ w ∉ s, x w = 1 then ∏ v ∈ s, gam (ψ v) (x v) else 0

theorem beta_insert {a : ι} {s : Finset ι} (ha : a ∉ s) (z : ∀ v, GL (Fin k) (Fq v)) :
    beta ψ (insert a s) z = ∑ y, gam (ψ a) y * beta ψ s ((Pi.mulSingle a y)⁻¹ * z) := by
  have hz : (Pi.mulSingle a (z a))⁻¹ * z = Function.update z a 1 := by
    funext w
    rcases eq_or_ne w a with rfl | hw <;> simp [Pi.mulSingle_eq_of_ne, *]
  rw [Finset.sum_eq_single (z a), hz]
  · have hs : ∏ v ∈ s, gam (ψ v) (Function.update z a 1 v) = ∏ v ∈ s, gam (ψ v) (z v) :=
      Finset.prod_congr rfl fun v hv => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hv ha)]
    have hc : (∀ w ∉ insert a s, z w = 1) ↔ ∀ w ∉ s, Function.update z a 1 w = 1 :=
      forall_congr' fun w => by rcases eq_or_ne w a with rfl | hw <;> simp [*]
    simp only [beta, ← hc, hs, Finset.prod_insert ha, mul_ite, mul_zero]
  · intro y _ hy
    rw [beta, ite_eq_right fun h => hy ?_, mul_zero]
    simpa [inv_mul_eq_one] using h a ha
  · simp

theorem sum_beta_insert {a : ι} {s : Finset ι} (ha : a ∉ s) (w : V) :
    ∑ x, beta ψ (insert a s) x • π x w = placeOp ψ π a (∑ x, beta ψ s x • π x w) := by
  simp_rw [placeOp, LinearMap.sum_apply, LinearMap.smul_apply, beta_insert ψ ha, Finset.sum_smul,
    map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Fintype.sum_equiv (Equiv.mulLeft (Pi.mulSingle a y)⁻¹) _ _ fun z => ?_
  simp only [Equiv.coe_mulLeft]
  rw [mul_smul, ← mul_apply_eq_comp (F := Module.End ℂ V), ← map_mul, mul_inv_cancel_left]

theorem prod_formula' : ProdFormula := by
  intro ι _ Fq _ _ k ψ V _ _ π μ w hμ
  have key (s : Finset ι) : ∑ x, beta ψ s x • π x w = (∏ v ∈ s, μ v) • w := by
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_eq_single 1 (fun b _ hb => ?_) (by simp)]
      · simp [beta]
      · rw [beta, ite_eq_right fun h => hb (funext fun v => h v (by simp)), zero_smul]
    | @insert a s ha ih =>
      rw [sum_beta_insert ψ π ha w, ih, map_smul, hμ, smul_smul, Finset.prod_insert ha, mul_comm]
  rw [← key]
  simp [totOp, beta, gamProd]

end PI.GGMatBoundW
