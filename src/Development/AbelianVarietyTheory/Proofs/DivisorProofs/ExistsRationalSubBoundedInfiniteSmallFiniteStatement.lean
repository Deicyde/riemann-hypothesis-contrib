module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalSubBoundedInfiniteSmallFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_sub_bounded_infinite_small_finite : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (U : Set (Af E)), U ∈ nhds (0 : Af E) → ∃ R : ℝ, 0 ≤ R ∧ ∀ x : Ad E, ∃ ξ : E, ‖pInf E (x - algebraMap E (Ad E) ξ)‖ ≤ R ∧ pFin E (x - algebraMap E (Ad E) ξ) ∈ U := by
  exact @GlobalTheory.AdeleApprox.exists_rat_sub_bounded_small
