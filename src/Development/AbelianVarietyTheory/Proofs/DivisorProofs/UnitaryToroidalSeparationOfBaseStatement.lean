module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToroidalSeparationOfBase
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt

@[expose] public section

open GlobalTheory.UChart

theorem _root_.GlobalTheory.T.unitaryToroidalSeparation_of_base : UStB := by
  first | exact @GlobalTheory.UPoincTop.uStB | exact GlobalTheory.UPoincTop.uStB | (intros; apply GlobalTheory.UPoincTop.uStB <;> assumption)
