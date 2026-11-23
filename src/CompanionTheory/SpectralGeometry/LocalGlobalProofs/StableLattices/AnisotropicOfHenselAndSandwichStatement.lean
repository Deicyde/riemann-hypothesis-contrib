module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AnisotropicOfHenselAndSandwich
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich

@[expose] public section

open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anisotropic_of_hensel_and_sandwich : StHensel → StSandwich → StAniso := by
  exact @GlobalTheory.CompanionTheory.HermAniso.aniso
