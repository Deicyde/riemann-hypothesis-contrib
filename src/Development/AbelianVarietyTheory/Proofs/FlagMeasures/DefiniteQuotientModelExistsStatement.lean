module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteQuotientModelExists
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definite_quotient_model_exists : GlobalTheory.TypeAsm.EmbC := by
  exact @GlobalTheory.TypeAsm.embC
