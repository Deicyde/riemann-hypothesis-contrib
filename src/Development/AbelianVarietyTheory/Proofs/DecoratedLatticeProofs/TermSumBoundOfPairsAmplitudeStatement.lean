module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TermSumBoundOfPairsAmplitude
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TermSumBoundOfPairsAmplitude

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deg_termSumBoundOfPairsAmplitude : GlobalTheory.Core.Deg.TermSumBoundOfPairsAmplitude := by
  exact @GlobalTheory.Core.Deg.termSumBound_of_pairsAmplitude
