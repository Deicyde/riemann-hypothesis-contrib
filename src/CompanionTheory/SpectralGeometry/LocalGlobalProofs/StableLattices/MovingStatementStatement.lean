module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MovingStatement
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite

@[expose] public section

open CompanionTheory.Rg.Fl

theorem _root_.GlobalTheory.T.MovingStatement : StMove := by
  first | exact @GlobalTheory.CompanionTheory.CartanMove.stMove | exact GlobalTheory.CompanionTheory.CartanMove.stMove | (intros; apply GlobalTheory.CompanionTheory.CartanMove.stMove <;> assumption)
