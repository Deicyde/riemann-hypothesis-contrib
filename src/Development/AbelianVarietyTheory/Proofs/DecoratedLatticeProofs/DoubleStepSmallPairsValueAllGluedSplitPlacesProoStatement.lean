module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepSmallPairsValueAllGluedSplitPlacesProo
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStepSmallPairsValueAllGluedSplitPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.VertexAll D := by
  exact @GlobalTheory.FinPl.vertexAll
