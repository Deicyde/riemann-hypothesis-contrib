module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeTermAdaptedNormalForm
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

@[expose] public section


theorem _root_.GlobalTheory.T.rowLattice_term_adaptedNormalForm : GlobalTheory.TypeAsm.TermC := by
  first | exact @GlobalTheory.TermRow.termC_holds | exact GlobalTheory.TermRow.termC_holds | (intros; apply GlobalTheory.TermRow.termC_holds <;> assumption)
