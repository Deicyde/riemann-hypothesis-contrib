module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedNormalFormRelevantTermProof
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adaptedNormalForm_relevantTerm : GlobalTheory.TypeAsm.NFExC := by
  exact @GlobalTheory.TypeAsm.nfExC_holds
