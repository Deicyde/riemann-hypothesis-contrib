module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Solvable
import Mathlib.Data.SetLike.Fintype
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.Perm.Cycle.Type

@[expose] public section

theorem Group.IsSolvable.exists_normal_subgroup_index_prime (Γ : Type) [Group Γ] [Finite Γ] [Nontrivial Γ] [Group.IsSolvable Γ] :
    ∃ M : Subgroup Γ, M.Normal ∧ M.index.Prime := by
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom (commutator Γ)).resolve_left
    (Group.IsSolvable.commutator_lt_top_of_nontrivial Γ).ne
  have hn : M.Normal := ⟨fun n hn g => by
    have h1 : g * n * g⁻¹ * n⁻¹ ∈ M := hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    simpa using M.mul_mem h1 hn⟩
  refine ⟨M, hn, ?_⟩
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (n := Nat.card (Γ ⧸ M)) (mt Subgroup.index_eq_one.1 hM.1)
  have := Fact.mk hp
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  have h1 : (Subgroup.zpowers g).comap (QuotientGroup.mk' M) = ⊤ := by
    refine hM.2 _ (lt_of_le_of_ne (fun x hx => ?_) fun e => ?_)
    · rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
      exact one_mem _
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M g
      have hx : x ∈ M := e ▸ Subgroup.mem_zpowers _
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx, orderOf_one] at hg
      exact hp.one_lt.ne hg
  have h2 : Subgroup.zpowers g = ⊤ :=
    Subgroup.comap_injective (QuotientGroup.mk'_surjective M) (h1.trans (Subgroup.comap_top _).symm)
  rw [Subgroup.index, ← Subgroup.card_top, ← h2, Nat.card_zpowers, hg]
  exact hp
