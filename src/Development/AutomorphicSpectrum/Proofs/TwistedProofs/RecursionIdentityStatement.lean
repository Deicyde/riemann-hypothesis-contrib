module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.RecursionIdentity
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.recursion_identity : Step := by
  exact @GlobalTheory.CompanionTheory.InertLevi.step
