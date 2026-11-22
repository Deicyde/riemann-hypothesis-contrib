module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.RecursionIdentity
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.recursion_identity : Step := by
  first | exact @GlobalTheory.CompanionTheory.InertLevi.step | exact GlobalTheory.CompanionTheory.InertLevi.step | (intros; apply GlobalTheory.CompanionTheory.InertLevi.step <;> assumption)
