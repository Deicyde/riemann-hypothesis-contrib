module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.Reindex
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.PermRepApply
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.IrreducibleOfMinimal

@[expose] public section

open Classical Formalism.L2.SG.GGMirabolic

namespace PI.GGMatBoundW

variable {ι : Type} {Fq : ι → Type} [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] {k : ℕ}
  (ψ : ∀ v, AddChar (Fq v) ℂ) {V : Type} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V)

theorem sum_conj_comm {H G : Type} [Group H] [Fintype H] [Group G] (ρ : Representation ℂ G V)
    (φ : H →* G) (f : H → ℂ) (hf : ∀ a x, f (a * x * a⁻¹) = f x) (g : G) (a : H)
    (hg : ∀ x, g * φ x * g⁻¹ = φ (a * x * a⁻¹)) :
    ρ g ∘ₗ ∑ x, f x • ρ (φ x) = (∑ x, f x • ρ (φ x)) ∘ₗ ρ g := by
  show ρ g * _ = _ * ρ g
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Fintype.sum_equiv (MulAut.conj a).toEquiv _ _ fun x => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, hf, ← hg,
    mul_smul_comm, smul_mul_assoc, ← map_mul, inv_mul_cancel_right]

theorem totOp_comm [Fintype ι] (g : ∀ v, GL (Fin k) (Fq v)) :
    π g ∘ₗ totOp ψ π = totOp ψ π ∘ₗ π g :=
  sum_conj_comm π (MonoidHom.id _) (gamProd ψ)
    (fun a x => Finset.prod_congr rfl fun v _ => PI.GGConvScalarW.gam_conj (ψ v) (a v) (x v))
    g g fun _ => rfl

theorem placeOp_comm (v : ι) (g : ∀ v, GL (Fin k) (Fq v)) :
    π g ∘ₗ placeOp ψ π v = placeOp ψ π v ∘ₗ π g := by
  refine sum_conj_comm π (MonoidHom.mulSingle _ v) (gam (ψ v))
    (PI.GGConvScalarW.gam_conj (ψ v)) g (g v) fun y => funext fun w => ?_
  rcases eq_or_ne w v with rfl | h <;> simp [Pi.mulSingle_eq_of_ne, *]

theorem joint_eigenvector_exists : JointEig := by
  intro ι _ Fq _ _ k ψ V _ _ _ π w μ hw hμ
  obtain ⟨W, hWE, hW0, hmin⟩ := exists_minimal_le (eigenSubrep _ (totOp_comm ψ π) μ)
    (ne_bot_of_mem (mem_eigenSubrep.2 hμ) hw)
  have hW0' := toSubmodule_ne_bot.2 hW0
  refine ⟨W.toSubmodule, hW0', W.apply_mem_toSubmodule, fun x hx => mem_eigenSubrep.1 (hWE hx),
    fun v => ?_⟩
  have hmaps : ∀ x ∈ W.toSubmodule, placeOp ψ π v x ∈ W.toSubmodule := fun x hx => by
    rw [placeOp, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (W.apply_mem_toSubmodule _ hx)
  have := Submodule.nontrivial_iff_ne_bot.2 hW0'
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((placeOp ψ π v).restrict hmaps)
  obtain ⟨u, hev⟩ := hc.exists_hasEigenvector
  have hu : (u : V) ∈ (W ⊓ eigenSubrep _ (placeOp_comm ψ π v) c).toSubmodule :=
    Submodule.mem_inf.2 ⟨u.2, mem_eigenSubrep.2 (congrArg Subtype.val hev.apply_eq_smul)⟩
  have hle := hmin _ (ne_bot_of_mem hu fun h0 => hev.2 (Subtype.ext h0)) inf_le_left
  exact ⟨c, fun x hx => mem_eigenSubrep.1 (inf_eq_left.1 hle hx)⟩

end PI.GGMatBoundW
