module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentCovolumeFiniteBounded
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

@[expose] public section


theorem _root_.GlobalTheory.T.integralUnipotent_covolume_finite_bounded : GlobalTheory.TypeAsm.CovNC := by
  first | exact @GlobalTheory.TypeAsm.covNC_holds | exact GlobalTheory.TypeAsm.covNC_holds | (intros; apply GlobalTheory.TypeAsm.covNC_holds <;> assumption)
