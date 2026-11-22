module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsAllPrimesOfClosedFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstClosedPts

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.divisorsOfConstantsAllPrimes_of_closedFibre : GlobalTheory.VertUnits.DivConstLocal → GlobalTheory.VertUnits.DivConstAll := by
  first | exact @GlobalTheory.VertUnits.divConstAll_of_divConstLocal | exact GlobalTheory.VertUnits.divConstAll_of_divConstLocal | (intros; apply GlobalTheory.VertUnits.divConstAll_of_divConstLocal <;> assumption)
