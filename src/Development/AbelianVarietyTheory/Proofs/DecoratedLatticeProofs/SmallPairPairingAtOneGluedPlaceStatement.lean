module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallPairPairingAtOneGluedPlace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallPair_pairing_at_one_gluedPlace : ∀ D : D7, GlobalTheory.FinPl.SmallOne D := by
  exact @GlobalTheory.FinPl.smallOne
