module

public import Mathlib

@[expose] public section

namespace UpperTheory.Reformulated.B.RegularUnitPoints

open AlgebraicGeometry CategoryTheory

theorem aux1 {Ω : Type} [Field Ω] : IsLocalRing Ω :=
  inferInstance

noncomputable def genPt {X : Scheme} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) : X :=
  ξ (IsLocalRing.closedPoint Ω)

noncomputable def Cpt {X : Scheme} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Type :=
  {p : X // genPt ξ ⤳ p}

theorem aux4 {X : Scheme} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    genPt ξ ⤳ p.1 :=
  p.2

theorem aux5 {Ω : Type} [Field Ω] : IsLocalRing (CommRingCat.of Ω) := by
  show IsLocalRing Ω
  infer_instance

noncomputable def genMap {X : Scheme} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    X.presheaf.stalk p.1 →+* Ω :=
  letI := aux5 (Ω := Ω)
  (X.presheaf.stalkSpecializes (aux4 ξ p) ≫ Scheme.stalkClosedPointTo ξ).hom

noncomputable def regAt {X : Scheme} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) : Subring Ω :=
  (genMap ξ p).range

noncomputable def unitAt {X : Scheme} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (a : Ω) : Prop :=
  a ≠ 0 ∧ a ∈ regAt ξ p ∧ a⁻¹ ∈ regAt ξ p

noncomputable def InFibre {X : Scheme} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : ℕ) (q : Cpt ξ) : Prop :=
  ¬ unitAt ξ q (p : Ω)

theorem main {X : Scheme} {Ω : Type} [Field Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {q : Cpt ξ}
    (hq : ∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) (n : ℕ) (hn : n ≠ 0) :
    unitAt ξ q (n : Ω) := by
  have key : ∀ m : ℕ, m ≠ 0 → unitAt ξ q (m : Ω) := by
    intro m
    induction m using Nat.recOnMul with
    | zero => intro h; exact absurd rfl h
    | one =>
      intro _
      refine ⟨by simp, ?_, ?_⟩
      · simp [(regAt ξ q).one_mem]
      · simp [(regAt ξ q).one_mem]
    | prime p hp =>
      intro _
      have := hq p hp
      unfold InFibre at this
      exact not_not.mp this
    | mul a b ha hb =>
      intro hab
      have ha0 : a ≠ 0 := by rintro rfl; simp at hab
      have hb0 : b ≠ 0 := by rintro rfl; simp at hab
      obtain ⟨a1, a2, a3⟩ := ha ha0
      obtain ⟨b1, b2, b3⟩ := hb hb0
      refine ⟨?_, ?_, ?_⟩
      · push_cast; exact mul_ne_zero a1 b1
      · push_cast; exact Subring.mul_mem _ a2 b2
      · push_cast; rw [mul_inv]; exact Subring.mul_mem _ a3 b3
  exact key n hn

end UpperTheory.Reformulated.B.RegularUnitPoints
