module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ModularityStatement
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite

@[expose] public section

open CompanionTheory.Rg.Fl

theorem _root_.GlobalTheory.T.ModularityStatement : StMod := by
  first | exact @GlobalTheory.CompanionTheory.HeckeCoinv.stMod | exact GlobalTheory.CompanionTheory.HeckeCoinv.stMod | (intros; apply GlobalTheory.CompanionTheory.HeckeCoinv.stMod <;> assumption)
