module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistRamifiedIffScalarFormsRamified
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistRamified_iff_scalarFormsRamified : GlobalTheory.AdForm.TwRam' := by
  exact @GlobalTheory.AdForm.ram_iff_scalar_ram
