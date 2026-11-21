module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TransferStatementBis
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite

@[expose] public section

open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.TransferStatementBis : StTransfer := by
  exact @GlobalTheory.CompanionTheory.HeckeTransfer.stTransfer
