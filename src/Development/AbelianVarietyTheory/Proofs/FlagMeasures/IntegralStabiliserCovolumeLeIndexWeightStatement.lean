module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralStabiliserCovolumeLeIndexWeight
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralStabiliser_covolume_le_indexWeight : GlobalTheory.TypeAsm.CovTC := by
  exact @GlobalTheory.TypeAsm.covTC_holds
