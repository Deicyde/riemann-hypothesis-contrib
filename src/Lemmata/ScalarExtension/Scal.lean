module

public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic

@[expose] public section

namespace Bl.ScalarIdentities

theorem goal1 {K A : Type} [Field K] [IsAlgClosed K] [Ring A] [Algebra K A]
    (S0 : Type) [AddCommGroup S0] [Module K S0] [Module A S0] [IsScalarTower K A S0]
    [FiniteDimensional K S0] [IsSimpleModule A S0] (φ : S0 →ₗ[K] S0) :
    ∃ u : A, ∀ v : S0, u • v = φ v := by
  let f : Module.End (Module.End A S0) S0 :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun g v => by
        obtain ⟨c, rfl⟩ :=
          (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed K).2 g
        exact φ.map_smul c v }
  have : Module.Finite (Module.End A S0) S0 :=
    Module.Finite.of_restrictScalars_finite K (Module.End A S0) S0
  obtain ⟨u, hu⟩ :=
    Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) (M := S0) f
  exact ⟨u, fun v => LinearMap.congr_fun hu v⟩

end Bl.ScalarIdentities
