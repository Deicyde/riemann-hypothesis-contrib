module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FactorizationStatement
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite

@[expose] public section

open CompanionTheory.Rg.Fl

theorem _root_.GlobalTheory.T.FactorizationStatement : StFactor := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stFactor | exact GlobalTheory.CompanionTheory.RgFl.stFactor | (intros; apply GlobalTheory.CompanionTheory.RgFl.stFactor <;> assumption)
