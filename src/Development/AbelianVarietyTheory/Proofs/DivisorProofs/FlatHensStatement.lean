module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder

@[expose] public section

open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_hens' : ∀ (R : Type) [CommRing R] [IsLocalRing R], Module.Flat R (Hens R) := by
  exact @GlobalTheory.Henselisation.flat_hens
