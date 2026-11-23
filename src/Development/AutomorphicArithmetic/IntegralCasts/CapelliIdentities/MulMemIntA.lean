module

public import Mathlib

@[expose] public section

namespace UpperTheory.Reformulated.B.Uc13

@[reducible] noncomputable def Af (F : Type) [Field F] [NumberField F] : Type :=
  IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F

@[reducible] noncomputable def Fv (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) : Type :=
  IsDedekindDomain.HeightOneSpectrum.adicCompletion F v

theorem aux3 (F : Type) [Field F] [NumberField F]
    (i : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    SubringClass (ValuationSubring (IsDedekindDomain.HeightOneSpectrum.adicCompletion F i))
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion F i) := by
  infer_instance

theorem aux4 (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (x : F) :
    (RestrictedProduct.evalRingHom
        (fun w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) =>
          w.adicCompletion F) v : Af F →+* Fv F v)
      (algebraMap F (Af F) x) =
    algebraMap F (Fv F v) x :=
  rfl

noncomputable def evalV (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    Af F →ₐ[F] Fv F v :=
  { (RestrictedProduct.evalRingHom
      (fun w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) =>
        w.adicCompletion F) v : Af F →+* Fv F v) with
    commutes' := aux4 F v }

noncomputable def intAf (F : Type) [Field F] [NumberField F] : Set (Af F) :=
  {a : Af F |
    ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      evalV F v a ∈ v.adicCompletionIntegers F}

noncomputable def intA (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    AddSubgroup (TensorProduct F (Af F) E) :=
  AddSubgroup.closure
    {y : TensorProduct F (Af F) E |
      ∃ a ∈ intAf F, ∃ x : NumberField.RingOfIntegers E, y = TensorProduct.tmul F a x.val}

private theorem intAf_mul (F : Type) [Field F] [NumberField F]
    {a b : Af F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a * b ∈ intAf F := by
  intro v
  rw [map_mul]
  exact mul_mem (ha v) (hb v)

theorem mul_mem_intA (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {x y : TensorProduct F (Af F) E}
    (hx : x ∈ intA F E) (hy : y ∈ intA F E) :
    x * y ∈ intA F E := by
  unfold intA at *
  induction hx, hy using AddSubgroup.closure_induction₂ with
  | mem _ _ hx hy =>
    obtain ⟨a, ha, s, rfl⟩ := hx
    obtain ⟨b, hb, t, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨a * b, intAf_mul F ha hb, s * t, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    rfl
  | zero_left _ _ => rw [zero_mul]; exact zero_mem _
  | zero_right _ _ => rw [mul_zero]; exact zero_mem _
  | add_left _ _ _ _ _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | add_right _ _ _ _ _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg_left _ _ _ _ h => rw [neg_mul]; exact neg_mem h
  | neg_right _ _ _ _ h => rw [mul_neg]; exact neg_mem h

end UpperTheory.Reformulated.B.Uc13
