module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralStabiliserCovolumeLeIndexWeight
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

@[expose] public section


theorem _root_.GlobalTheory.T.integralStabiliser_covolume_le_indexWeight : GlobalTheory.TypeAsm.CovTC := by
  first | exact @GlobalTheory.TypeAsm.covTC_holds | exact GlobalTheory.TypeAsm.covTC_holds | (intros; apply GlobalTheory.TypeAsm.covTC_holds <;> assumption)
