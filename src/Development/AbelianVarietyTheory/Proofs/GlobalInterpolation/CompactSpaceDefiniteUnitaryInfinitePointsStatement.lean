module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CompactSpaceDefiniteUnitaryInfinitePoints
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactSpace_definiteUnitaryInfinitePoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), CompactSpace (infU E n) := by
  exact @GlobalTheory.InfUCompact.compactSpace_infU
