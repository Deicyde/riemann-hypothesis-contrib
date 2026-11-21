module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFrameSelfNormalFormExistsProof
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedFrameSelfNormalFormExists_proof : GlobalTheory.TypeAsm.IdNFC := by
  exact @GlobalTheory.IdNF.idNFC_holds
