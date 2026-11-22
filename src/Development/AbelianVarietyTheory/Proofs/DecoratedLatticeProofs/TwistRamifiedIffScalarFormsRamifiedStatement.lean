module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistRamifiedIffScalarFormsRamified
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt

@[expose] public section


theorem _root_.GlobalTheory.T.twistRamified_iff_scalarFormsRamified : GlobalTheory.AdForm.TwRam' := by
  first | exact @GlobalTheory.AdForm.ram_iff_scalar_ram | exact GlobalTheory.AdForm.ram_iff_scalar_ram | (intros; apply GlobalTheory.AdForm.ram_iff_scalar_ram <;> assumption)
