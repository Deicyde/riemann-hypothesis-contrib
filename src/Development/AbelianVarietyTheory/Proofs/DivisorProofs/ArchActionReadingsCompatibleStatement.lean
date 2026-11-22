module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.archActionReadings_compatible : GlobalTheory.RealLift.ActsLaws := by
  first | exact @GlobalTheory.RealLift.actsLaws | exact GlobalTheory.RealLift.actsLaws | (intros; apply GlobalTheory.RealLift.actsLaws <;> assumption)
