module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SandwichStatement
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich

@[expose] public section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.SandwichStatement : StSandwich := by
  first | exact @GlobalTheory.CompanionTheory.Lattice.stSandwich | exact GlobalTheory.CompanionTheory.Lattice.stSandwich | (intros; apply GlobalTheory.CompanionTheory.Lattice.stSandwich <;> assumption)
