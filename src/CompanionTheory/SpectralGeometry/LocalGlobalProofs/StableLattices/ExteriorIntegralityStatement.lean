module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorIntegrality
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

@[expose] public section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ExteriorIntegrality : WedgeInt := by
  exact @GlobalTheory.CompanionTheory.WedgeEmb.wedgeInt
