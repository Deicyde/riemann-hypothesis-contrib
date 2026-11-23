module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralizerSplitRankUpperBound
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

@[expose] public section

open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_splitRank_upper_bound : GlobalTheory.RegSS.SubtorusLaurent → GlobalTheory.RegSS.CharacterMonomial → GlobalTheory.RegSS.SeparatingPoints → GlobalTheory.RegSS.SplitRankUpper := by
  exact @GlobalTheory.RegSS.SplitRankBound.splitRankUpper
