module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRadicalCosetCountOfHeisenberg
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallRadicalCosetCount_of_heisenberg : Heis → LatIndex → TraceIndex → Count := by
  exact @GlobalTheory.InertZeta.count_of_heis
