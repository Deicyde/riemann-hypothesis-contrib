module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLocalRingPointedEtaleNeighbourhood
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder

@[expose] public section

open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_localRing_pointedEtaleNeighbourhood : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R), Module.Flat R i.B := by
  exact @GlobalTheory.Henselisation.EtNbhd.flat_B
