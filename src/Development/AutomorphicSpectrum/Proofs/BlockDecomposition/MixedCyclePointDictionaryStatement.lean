module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCyclePointDictionary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_cycle_point_dictionary : GlobalTheory.CompanionTheory.MixZ.PtDict := by
  exact @GlobalTheory.CompanionTheory.MixZ.ptDict
