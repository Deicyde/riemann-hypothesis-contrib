module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalisingConstantsProductHypProof
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisingConstantsProductHyp_proof : GlobalTheory.TypeAsm.ConstC := by
  exact @GlobalTheory.LocalConst.constC
