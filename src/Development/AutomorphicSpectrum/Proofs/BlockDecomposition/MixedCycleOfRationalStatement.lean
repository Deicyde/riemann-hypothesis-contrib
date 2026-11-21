module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleOfRational
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_cycle_of_rational : GlobalTheory.CompanionTheory.MixZ.CycleOfRat := by
  exact @GlobalTheory.CompanionTheory.MixZ.CycleRat.cycleOfRat
