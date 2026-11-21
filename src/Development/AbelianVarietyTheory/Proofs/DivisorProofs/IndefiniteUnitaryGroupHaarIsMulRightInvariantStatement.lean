module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryGroupHaarIsMulRightInvariant
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff

@[expose] public section

open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefiniteUnitaryGroup_haar_isMulRightInvariant : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  exact @GlobalTheory.haar_UJ_isMulRightInvariant
