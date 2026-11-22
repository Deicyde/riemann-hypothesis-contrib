module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLatticeBaseChangeSpanProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange

@[expose] public section


theorem _root_.GlobalTheory.T.dualWeylLattice_baseChange_span_proof : GlobalTheory.BaseCmp.NabBaseChange := by
  first | exact @GlobalTheory.NabBC.nabBaseChange | exact GlobalTheory.NabBC.nabBaseChange | (intros; apply GlobalTheory.NabBC.nabBaseChange <;> assumption)
