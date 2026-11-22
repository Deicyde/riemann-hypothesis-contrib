module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsMeanBoundOfGenusMean
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

@[expose] public section


theorem _root_.GlobalTheory.T.rowsMeanC_holds : GlobalTheory.TypeAsm.RowsMeanC := by
  first | exact @GlobalTheory.TypeAsm.rowsMean | exact GlobalTheory.TypeAsm.rowsMean | (intros; apply GlobalTheory.TypeAsm.rowsMean <;> assumption)
