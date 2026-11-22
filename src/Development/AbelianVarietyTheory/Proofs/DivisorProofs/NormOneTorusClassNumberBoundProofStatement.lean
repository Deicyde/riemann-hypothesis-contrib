module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneTorusClassNumberBoundProof
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound

@[expose] public section


theorem _root_.GlobalTheory.T.normOneTorusClassNumberBound_proof : GlobalTheory.UCls.TorusBound := by
  first | exact @GlobalTheory.UCls.torusBound | exact GlobalTheory.UCls.torusBound | (intros; apply GlobalTheory.UCls.torusBound <;> assumption)
