module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataAsCombinationsAtSplitPlacesProof
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.AllComb D := by
  exact @GlobalTheory.FinPl.allComb
