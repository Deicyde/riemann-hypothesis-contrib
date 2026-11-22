module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalisingConstantsProductHypProof
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC

@[expose] public section


theorem _root_.GlobalTheory.T.normalisingConstantsProductHyp_proof : GlobalTheory.TypeAsm.ConstC := by
  first | exact @GlobalTheory.LocalConst.constC | exact GlobalTheory.LocalConst.constC | (intros; apply GlobalTheory.LocalConst.constC <;> assumption)
