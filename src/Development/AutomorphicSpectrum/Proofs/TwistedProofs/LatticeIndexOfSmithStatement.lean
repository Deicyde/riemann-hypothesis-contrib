module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.LatticeIndexOfSmith
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_index_of_smith : Smith → LatIndex := by
  exact @GlobalTheory.CompanionTheory.InertIndex.latIndex
