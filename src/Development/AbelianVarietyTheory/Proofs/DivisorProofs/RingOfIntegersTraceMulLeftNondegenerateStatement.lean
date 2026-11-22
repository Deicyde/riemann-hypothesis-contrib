module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOfIntegersTraceMulLeftNondegenerate

@[expose] public section

open NumberField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.ringOfIntegers_eq_zero_of_trace_mulLeft_eq_zero : ∀ (K : Type) [Field K] [NumberField K] (x : 𝓞 K), (∀ y : 𝓞 K, LinearMap.trace ℤ (𝓞 K) (LinearMap.mulLeft ℤ (x * y)) = 0) → x = 0 := by
  first | (exact @GlobalTheory.ringOfIntegers_trace_mulLeft_nondegenerate) | (exact GlobalTheory.ringOfIntegers_trace_mulLeft_nondegenerate) | (intros; apply GlobalTheory.ringOfIntegers_trace_mulLeft_nondegenerate  <;> assumption)
