module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StTensor
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite

@[expose] public section

open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stTensor' : StTensor := by
  exact @GlobalTheory.CompanionTheory.RestT.stTensor
