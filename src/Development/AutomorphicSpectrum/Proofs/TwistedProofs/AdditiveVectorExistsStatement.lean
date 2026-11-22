module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.AdditiveVectorExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.additive_vector_exists : AddVec := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.addVec | exact GlobalTheory.CompanionTheory.InertZeta.addVec | (intros; apply GlobalTheory.CompanionTheory.InertZeta.addVec <;> assumption)
