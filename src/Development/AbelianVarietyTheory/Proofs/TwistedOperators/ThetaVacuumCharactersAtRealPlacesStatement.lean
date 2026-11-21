module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersAtRealPlaces
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaVacuumCharacters_atRealPlaces : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D := by
  exact @GlobalTheory.vacChar_of_record
