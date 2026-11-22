module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointGramMinorsAgreeProof
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

@[expose] public section


theorem _root_.GlobalTheory.T.realPointGramMinorsAgree_proof : GlobalTheory.TypeAsm.GramC := by
  first | exact @GlobalTheory.TypeAsm.gramC_holds | exact GlobalTheory.TypeAsm.gramC_holds | (intros; apply GlobalTheory.TypeAsm.gramC_holds <;> assumption)
