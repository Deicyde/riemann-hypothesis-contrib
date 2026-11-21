module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointedEtaleNeighbourhoodLocalRingIsDirected
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder

@[expose] public section

open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsDirected (EtNbhd R) (· ≤ ·) := by
  exact @GlobalTheory.Henselisation.etNbhd_isDirected
