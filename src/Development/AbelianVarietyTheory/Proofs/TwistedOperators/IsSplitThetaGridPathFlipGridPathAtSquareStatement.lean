module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSplitThetaGridPathFlipGridPathAtSquare
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

@[expose] public section

open GlobalTheory.SplitFlip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSplitThetaGridPath_flipGridPathAtSquare : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ → IsPath (flipPath i j γ) := by
  exact @GlobalTheory.SplitFlip.isPath_flipPath
