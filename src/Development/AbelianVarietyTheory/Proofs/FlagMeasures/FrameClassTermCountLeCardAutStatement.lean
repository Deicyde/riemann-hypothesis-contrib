module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameClassTermCountLeCardAut
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameClass_termCount_le_card_aut : GlobalTheory.TypeAsm.FibCardC := by
  exact @GlobalTheory.TypeAsm.FibCard.fibCardC
