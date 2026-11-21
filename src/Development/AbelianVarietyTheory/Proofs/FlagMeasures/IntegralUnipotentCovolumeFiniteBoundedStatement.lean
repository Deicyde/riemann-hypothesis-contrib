module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentCovolumeFiniteBounded
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnipotent_covolume_finite_bounded : GlobalTheory.TypeAsm.CovNC := by
  exact @GlobalTheory.TypeAsm.covNC_holds
