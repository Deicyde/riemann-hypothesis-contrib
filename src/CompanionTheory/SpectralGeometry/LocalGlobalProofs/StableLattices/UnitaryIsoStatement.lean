module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UnitaryIso
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

@[expose] public section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.UnitaryIso : UIso := by
  exact @GlobalTheory.CompanionTheory.ZuckUIso.uIso
