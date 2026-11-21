module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FixedVectorStatement
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite

@[expose] public section

open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.FixedVectorStatement : StFixVec := by
  exact @GlobalTheory.CompanionTheory.RgFl.stFixVec
