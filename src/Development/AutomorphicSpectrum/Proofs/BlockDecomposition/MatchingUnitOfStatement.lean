module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingUnitOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matching_unit_of : PositivityTheory.Rg.BcB.F.MLM.MatchLMUnitOf := by
  exact @GlobalTheory.CompanionTheory.MatchUnit.matchLMUnitOf
