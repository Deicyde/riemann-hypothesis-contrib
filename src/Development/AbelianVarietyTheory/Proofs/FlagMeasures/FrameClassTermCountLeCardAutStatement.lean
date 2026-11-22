module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameClassTermCountLeCardAut
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

@[expose] public section


theorem _root_.GlobalTheory.T.frameClass_termCount_le_card_aut : GlobalTheory.TypeAsm.FibCardC := by
  first | exact @GlobalTheory.TypeAsm.FibCard.fibCardC | exact GlobalTheory.TypeAsm.FibCard.fibCardC | (intros; apply GlobalTheory.TypeAsm.FibCard.fibCardC <;> assumption)
