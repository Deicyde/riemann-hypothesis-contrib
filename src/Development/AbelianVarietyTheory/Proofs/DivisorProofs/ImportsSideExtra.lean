module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussManinPeriodsHolds

@[expose] public section

namespace GlobalTheory.GaussManinTop

theorem main : GlobalTheory.Published.GaussManinPeriods :=
  GlobalTheory.PeriodFamily.gaussManinPeriods_holds

end GlobalTheory.GaussManinTop
