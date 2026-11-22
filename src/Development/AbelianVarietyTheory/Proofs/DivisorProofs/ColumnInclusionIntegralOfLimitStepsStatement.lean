module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionIntegralOfLimitSteps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

@[expose] public section

open GlobalTheory.IsoTriv

theorem _root_.GlobalTheory.T.columnInclusionIntegral_of_limitSteps : LimActSt → LimPtSt → LimFrameSt → InclSt := by
  first | exact @GlobalTheory.IsoTriv.Incl.inclSt_of_lim | exact GlobalTheory.IsoTriv.Incl.inclSt_of_lim | (intros; apply GlobalTheory.IsoTriv.Incl.inclSt_of_lim <;> assumption)
