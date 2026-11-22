module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapHypothesisOfLargenessConstantGe
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC

@[expose] public section


theorem _root_.GlobalTheory.T.gapC_holds : GlobalTheory.TypeAsm.GapC := by
  first | exact @GlobalTheory.TypeAsm.gapC | exact GlobalTheory.TypeAsm.gapC | (intros; apply GlobalTheory.TypeAsm.gapC <;> assumption)
