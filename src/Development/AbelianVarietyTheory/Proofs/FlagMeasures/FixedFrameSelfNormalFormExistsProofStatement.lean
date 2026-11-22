module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFrameSelfNormalFormExistsProof
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

@[expose] public section


theorem _root_.GlobalTheory.T.fixedFrameSelfNormalFormExists_proof : GlobalTheory.TypeAsm.IdNFC := by
  first | exact @GlobalTheory.IdNF.idNFC_holds | exact GlobalTheory.IdNF.idNFC_holds | (intros; apply GlobalTheory.IdNF.idNFC_holds <;> assumption)
