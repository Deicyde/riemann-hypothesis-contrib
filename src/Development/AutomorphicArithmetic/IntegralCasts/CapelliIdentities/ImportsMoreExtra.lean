module

public import Mathlib
public import Formalism.WeaklyAdmissibleFiltrations.Statement

@[expose] public section

namespace UpperTheory.Reformulated.B.Qh15

open scoped TensorProduct

theorem aux1 {A : Type} [CommRing A] : SMulCommClass A A A :=
  inferInstance

theorem aux2 {G A : Type} [Group G] [CommRing A] (κ : G →* Aˣ) :
    (κ 1 : A) • (LinearMap.id : A →ₗ[A] A) = 1 := by
  ext
  simp

theorem aux3 {G A : Type} [Group G] [CommRing A] (κ : G →* Aˣ) (g h : G) :
    (κ (g * h) : A) • (LinearMap.id : A →ₗ[A] A) =
      (κ g : A) • (LinearMap.id : A →ₗ[A] A) * (κ h : A) • (LinearMap.id : A →ₗ[A] A) := by
  ext
  simp [mul_comm]

noncomputable def chRep {G A : Type} [Group G] [CommRing A] (κ : G →* Aˣ) :
    Representation A G A where
  toFun g := (κ g : A) • (LinearMap.id : A →ₗ[A] A)
  map_one' := aux2 κ
  map_mul' := aux3 κ

theorem act_mul {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {E : Type} [Field E] [Algebra Qp E] (κ : G →* Eˣ) (g : G) (x y : E ⊗[Qp] B) :
    Formalism.WeaklyAdmissibleFiltrations.actVB PD (chRep κ) g x *
        Formalism.WeaklyAdmissibleFiltrations.actVB PD (chRep κ⁻¹) g y =
      Formalism.WeaklyAdmissibleFiltrations.actVB PD (chRep 1) g (x * y) := by
  have hch : ∀ (μ : G →* Eˣ) (a : E), chRep μ g a = (μ g : E) * a := fun μ a => rfl
  have hact : ∀ (μ : G →* Eˣ) (a : E) (b : B),
      Formalism.WeaklyAdmissibleFiltrations.actVB PD (chRep μ) g (a ⊗ₜ[Qp] b) =
        ((μ g : E) * a) ⊗ₜ[Qp] PD.actB g b := by
    intro μ a b
    rw [← hch]
    rfl
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => simp only [map_add (f := _), add_mul, h₁, h₂]
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => simp only [map_add (f := _), mul_add, h₁, h₂]
    | tmul c d =>
      have hu : (κ g : E) * a * ((κ⁻¹ g : E) * c) = ((1 : G →* Eˣ) g : E) * (a * c) := by
        rw [mul_mul_mul_comm, ← Units.val_mul, MonoidHom.inv_apply, mul_inv_cancel,
          MonoidHom.one_apply]
      rw [Algebra.TensorProduct.tmul_mul_tmul, hact, hact, hact,
        Algebra.TensorProduct.tmul_mul_tmul, hu, map_mul]

end UpperTheory.Reformulated.B.Qh15
