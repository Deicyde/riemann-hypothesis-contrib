module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedPointLengthFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_point_length_formula : GlobalTheory.CompanionTheory.MixZ.PtLen := by
  exact @GlobalTheory.CompanionTheory.MixZ.PtLenProof.ptLen
