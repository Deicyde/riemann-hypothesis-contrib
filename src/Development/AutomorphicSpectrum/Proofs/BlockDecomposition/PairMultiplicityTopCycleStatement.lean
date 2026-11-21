module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairMultiplicityTopCycle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient

@[expose] public section

open GlobalTheory.CompanionTheory.PairMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_multiplicity_top_cycle : GlobalTheory.CompanionTheory.PairMult.TopCyc := by
  exact @GlobalTheory.CompanionTheory.PairMult.TopCycQ.topCyc
