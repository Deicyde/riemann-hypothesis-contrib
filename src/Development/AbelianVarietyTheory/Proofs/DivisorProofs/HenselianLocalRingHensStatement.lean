module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianLocalRingHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder

@[expose] public section

open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.henselianLocalRing_hens' : ∀ (R : Type) [CommRing R] [IsLocalRing R], HenselianLocalRing (Hens R) := by
  exact @GlobalTheory.Henselisation.henselianLocalRing_hens
