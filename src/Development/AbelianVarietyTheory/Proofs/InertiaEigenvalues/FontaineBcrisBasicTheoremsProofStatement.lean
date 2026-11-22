module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBcrisBasicTheoremsProof
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero

@[expose] public section


theorem _root_.GlobalTheory.T.fontaineBcrisBasicTheorems_proof : GlobalTheory.Published.FontaineBcris := by
  first | exact @GlobalTheory.MemLoc.fontaineBcris | exact GlobalTheory.MemLoc.fontaineBcris | (intros; apply GlobalTheory.MemLoc.fontaineBcris <;> assumption)
