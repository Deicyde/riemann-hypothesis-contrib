module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusStatement
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich

@[expose] public section

open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.TorusStatement : StTor := by
  exact @GlobalTheory.CompanionTheory.FrameTorus.stTor
