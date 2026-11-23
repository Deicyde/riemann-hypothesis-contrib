module

public import Mathlib

@[expose] public section

theorem UpperTheory.Reformulated.B.NonvanishingPoint.exists_point_nonvanishing_reduced :
    ∀ (k : Type) [inst : Field k] [IsAlgClosed k] (B : Type)
    [inst_2 : CommRing B] [inst_3 : Algebra k B] [Algebra.FiniteType k B] [IsReduced B] {c : B},
    c ≠ (0 : B) → ∃ (x : B →ₐ[k] k), (x : B → k) c ≠ (0 : k) := by
  intro k _ _ B _ _ _ _ c hc
  have : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := k)
  have hj : (⊥ : Ideal B).jacobson = ⊥ :=
    IsJacobsonRing.out inferInstance Ideal.isRadical_bot
  have hcj : c ∉ (⊥ : Ideal B).jacobson := by
    rw [hj]
    exact fun h => hc ((Ideal.mem_bot).1 h)
  rw [Ideal.jacobson, Ideal.mem_sInf] at hcj
  push Not at hcj
  obtain ⟨m, ⟨-, hm⟩, hcm⟩ := hcj
  let : Field (B ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite k (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ m)
  let f : (B ⧸ m) →ₐ[k] k := IsAlgClosed.lift
  refine ⟨f.comp (Ideal.Quotient.mkₐ k m), ?_⟩
  intro h
  exact hcm (Ideal.Quotient.eq_zero_iff_mem.mp ((map_eq_zero f).mp h))
