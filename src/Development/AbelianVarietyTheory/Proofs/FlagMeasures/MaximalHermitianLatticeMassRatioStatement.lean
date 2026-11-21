module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeMassRatio
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass

@[expose] public section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalHermitianLattice_massRatio : MaxMass := by
  exact @GlobalTheory.Mass.MaxFormula.main
