module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeIdempotentConstantTermVanish
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typeIdempotent_constantTerm_vanish : GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish := by
  exact @GlobalTheory.TypeConstTerm.typeConstTermVanish
