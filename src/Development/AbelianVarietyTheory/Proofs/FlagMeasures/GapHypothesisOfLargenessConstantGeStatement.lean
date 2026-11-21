module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapHypothesisOfLargenessConstantGe
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gapC_holds : GlobalTheory.TypeAsm.GapC := by
  exact @GlobalTheory.TypeAsm.gapC
