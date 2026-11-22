module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteQuotientModelExists
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

@[expose] public section


theorem _root_.GlobalTheory.T.definite_quotient_model_exists : GlobalTheory.TypeAsm.EmbC := by
  first | exact @GlobalTheory.TypeAsm.embC | exact GlobalTheory.TypeAsm.embC | (intros; apply GlobalTheory.TypeAsm.embC <;> assumption)
