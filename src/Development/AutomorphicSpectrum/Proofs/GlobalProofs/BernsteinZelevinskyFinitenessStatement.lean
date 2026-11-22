module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible

@[expose] public section


theorem _root_.GlobalTheory.T.bernstein_zelevinsky_finiteness : GlobalTheory.Published.BernsteinZelevinskyFiniteness := by
  first | exact @GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness | exact GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness | (intros; apply GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness <;> assumption)
