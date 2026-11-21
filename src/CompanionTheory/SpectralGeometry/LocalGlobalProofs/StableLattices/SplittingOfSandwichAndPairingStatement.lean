module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SplittingOfSandwichAndPairing
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich

@[expose] public section

open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitting_of_sandwich_and_pairing : StSandwich → StPairing → StSplit := by
  exact @GlobalTheory.CompanionTheory.RgSplit.stSplit
