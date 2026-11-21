module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryHeisenbergRadicalCoordinates
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_heisenberg_radical_coordinates : Heis := by
  exact @GlobalTheory.InertZeta.HeisCoord.Heisenberg₂
