module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.CountOfHeisenbergIndex
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.count_of_heisenberg_index : Heis → LatIndex → TraceIndex → Count := by
  exact @GlobalTheory.CompanionTheory.InertCount.count
