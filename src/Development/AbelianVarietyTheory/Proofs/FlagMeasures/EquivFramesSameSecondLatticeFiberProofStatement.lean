module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivFramesSameSecondLatticeFiberProof
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivFramesSameSecondLatticeFiber_proof : GlobalTheory.TypeAsm.FibC := by
  exact @GlobalTheory.TypeAsm.FibProof.fibC
