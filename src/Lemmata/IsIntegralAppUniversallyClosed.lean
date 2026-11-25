module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

private theorem isIntegral_of_iso_comp {A B C E : CommRingCat.{0}} (i : A ⟶ B) (f : B ⟶ C) (m : C ⟶ E) [IsIso i]
    [IsIso m] (h : (i ≫ f ≫ m).hom.IsIntegral) : f.hom.IsIntegral := by
  have e : f = inv i ≫ (i ≫ f ≫ m) ≫ inv m := by simp
  rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp]
  refine RingHom.IsIntegral.trans _ _ ?_ (RingHom.IsIntegral.trans _ _ h ?_)
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv i)).2
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv m)).2

theorem AlgebraicGeometry.isIntegral_app_of_universallyClosed {Z₁ Z₂ : Scheme.{0}} (ρ : Z₁ ⟶ Z₂) [UniversallyClosed ρ]
    (V : Z₂.Opens) (hV : IsAffineOpen V) : (ρ.app V).hom.IsIntegral := by
  have : IsAffine V.toScheme := hV
  have h := isIntegral_appTop_of_universallyClosed (ρ ∣_ V)
  rw [morphismRestrict_appTop] at h
  have e : V.ι ''ᵁ ⊤ = V := by simp
  rw [ρ.app_eq e, Category.assoc, Category.assoc, ← Functor.map_comp] at h
  simp only [eqToHom_op, eqToHom_map, eqToHom_trans] at h
  have hi : ∀ {A B : CommRingCat.{0}} (q : A = B), IsIso (eqToHom q) := fun q => by
    subst q; rw [eqToHom_refl]; infer_instance
  exact @isIntegral_of_iso_comp _ _ _ _ _ _ _ (hi _) (hi _) h
