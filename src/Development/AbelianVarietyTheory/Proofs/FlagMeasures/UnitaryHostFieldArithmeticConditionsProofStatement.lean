module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProof
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

@[expose] public section


theorem _root_.GlobalTheory.T.unitaryHostFieldArithmeticConditions : GlobalTheory.TypeAsm.HostC := by
  first | exact @GlobalTheory.TypeAsm.hostC | exact GlobalTheory.TypeAsm.hostC | (intros; apply GlobalTheory.TypeAsm.hostC <;> assumption)
