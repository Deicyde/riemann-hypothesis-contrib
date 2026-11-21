module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeTermAdaptedNormalForm
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowLattice_term_adaptedNormalForm : GlobalTheory.TypeAsm.TermC := by
  exact @GlobalTheory.TermRow.termC_holds
