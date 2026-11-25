module

public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

theorem RingHom.Flat.map_mem_nonZeroDivisors {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) (hφ : φ.Flat) {a : A}
    (ha : a ∈ nonZeroDivisors A) : φ a ∈ nonZeroDivisors R := by
  algebraize [φ]
  have hreg : IsSMulRegular R a := Module.Flat.isSMulRegular_of_nonZeroDivisors ha
  refine mem_nonZeroDivisors_iff_right.2 fun x hx => hreg ?_
  change a • x = a • (0 : R)
  rw [Algebra.smul_def, smul_zero, mul_comm]
  exact hx
