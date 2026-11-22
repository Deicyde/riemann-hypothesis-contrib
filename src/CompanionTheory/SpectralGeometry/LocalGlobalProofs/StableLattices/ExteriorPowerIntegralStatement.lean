module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorPowerIntegral
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

@[expose] public section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

theorem _root_.GlobalTheory.T.ExteriorPowerIntegral : OKWedge := by
  first | exact @GlobalTheory.CompanionTheory.ZuckWedge.okWedge | exact GlobalTheory.CompanionTheory.ZuckWedge.okWedge | (intros; apply GlobalTheory.CompanionTheory.ZuckWedge.okWedge <;> assumption)
