module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermPairsRowLatticeCountedViaEmbeddings
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.termPairs_rowLattice_counted_via_embeddings : GlobalTheory.TypeAsm.PerRowC := by
  exact @GlobalTheory.TypeAsm.perRowC
