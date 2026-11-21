module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingSplitOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchT

@[expose] public section

open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matching_split_of : MatchSplitOf := by
  exact @GlobalTheory.CompanionTheory.MatchPowers.matchSplitOf
