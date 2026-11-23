module

public import Mathlib

@[expose] public section

theorem UpperTheory.fixed_quadratic_mem_base :
    ∀ {F E : Type} [Field F] [Field E] [Algebra F E], Module.finrank F E = 2 → ∀ (σ : E →ₐ[F] E) (α : E), σ α ≠ α → ∀ x, σ x = x → x ∈ (algebraMap F E).range := by
  intro F E _ _ _ h σ α hα x hx
  by_contra hxr
  have hfin : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have li : LinearIndependent F ![x, (1 : E)] := by
    rw [linearIndependent_fin2]
    refine ⟨by simp, fun a ha => hxr ⟨a, ?_⟩⟩
    simpa [Algebra.smul_def] using ha
  have hspan : Submodule.span F (Set.range ![x, (1 : E)]) = ⊤ :=
    li.span_eq_top_of_card_eq_finrank' (by simp [h])
  have heq : σ.toLinearMap = LinearMap.id := by
    apply LinearMap.ext_on_range hspan
    intro i
    fin_cases i <;> simp [hx]
  exact hα (LinearMap.congr_fun heq α)
