module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOverRowCompatible
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.termsOverRow_compatible : GlobalTheory.TypeAsm.CompatC := by
  exact @GlobalTheory.TypeAsm.CompatPf.compatC
