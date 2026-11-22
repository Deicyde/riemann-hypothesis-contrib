module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIwasawaCosetSurjOfLeviElementExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.unitaryIwasawaCosetSurj_of_leviElementExists : LeviExists → CosetSurj := by
  first | exact @GlobalTheory.InertZeta.cosetSurj_of_leviExists | exact GlobalTheory.InertZeta.cosetSurj_of_leviExists | (intros; apply GlobalTheory.InertZeta.cosetSurj_of_leviExists <;> assumption)
