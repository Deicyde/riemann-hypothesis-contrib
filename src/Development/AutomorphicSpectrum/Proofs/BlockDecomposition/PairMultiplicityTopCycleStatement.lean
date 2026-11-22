module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairMultiplicityTopCycle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient

@[expose] public section

open GlobalTheory.CompanionTheory.PairMult

theorem _root_.GlobalTheory.T.pair_multiplicity_top_cycle : GlobalTheory.CompanionTheory.PairMult.TopCyc := by
  first | exact @GlobalTheory.CompanionTheory.PairMult.TopCycQ.topCyc | exact GlobalTheory.CompanionTheory.PairMult.TopCycQ.topCyc | (intros; apply GlobalTheory.CompanionTheory.PairMult.TopCycQ.topCyc <;> assumption)
