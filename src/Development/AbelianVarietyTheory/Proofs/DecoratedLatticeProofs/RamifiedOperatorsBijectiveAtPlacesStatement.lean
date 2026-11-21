module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorsBijectiveAtPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epsilonFourierProduct_bijective_gluedPlaces : ∀ D : D7, GlobalTheory.FinPl.AllBijective D := by
  exact @GlobalTheory.FinPl.allBijective_all
