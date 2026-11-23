module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRadicalCosetCountOfHeisenberg

@[expose] public section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.count_of_heisenberg_index : Heis → LatIndex → TraceIndex → Count :=
  GlobalTheory.InertZeta.count_of_heis
