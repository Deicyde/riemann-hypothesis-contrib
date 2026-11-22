module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DefinitenessStatement
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite

@[expose] public section

open CompanionTheory.Rg.Fl

theorem _root_.GlobalTheory.T.DefinitenessStatement : StDefinite := by
  first | exact @GlobalTheory.CompanionTheory.DefiniteForm.stDefinite | exact GlobalTheory.CompanionTheory.DefiniteForm.stDefinite | (intros; apply GlobalTheory.CompanionTheory.DefiniteForm.stDefinite <;> assumption)
