module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompactSpaceMaximalCompactUnitaryInfinite
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd

@[expose] public section

open GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactSpace_maximalCompact_unitary_infinite : ∀ (E : Type) [Field E] (a : ℕ), CompactSpace (Kinf E a) := by
  exact @GlobalTheory.KinfCompactness.compactSpace_Kinf
