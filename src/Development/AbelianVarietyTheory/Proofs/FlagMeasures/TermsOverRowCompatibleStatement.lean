module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOverRowCompatible
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

@[expose] public section


theorem _root_.GlobalTheory.T.termsOverRow_compatible : GlobalTheory.TypeAsm.CompatC := by
  first | exact @GlobalTheory.TypeAsm.CompatPf.compatC | exact GlobalTheory.TypeAsm.CompatPf.compatC | (intros; apply GlobalTheory.TypeAsm.CompatPf.compatC <;> assumption)
