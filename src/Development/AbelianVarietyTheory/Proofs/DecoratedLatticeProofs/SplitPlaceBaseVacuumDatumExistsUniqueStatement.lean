module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique : ∀ D : D7, GlobalTheory.FinPl.OverBasic D := by
  exact @GlobalTheory.FinPl.overBasic
