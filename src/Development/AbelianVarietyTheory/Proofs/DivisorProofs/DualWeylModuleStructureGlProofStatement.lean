module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylModuleStructureGlProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

@[expose] public section

open GlobalTheory.LeviCut

theorem _root_.GlobalTheory.T.dualWeylModuleStructureGl_proof : GlobalTheory.LeviCut.NablaGl := by
  first | exact @GlobalTheory.LeviCut.nablaGl | exact GlobalTheory.LeviCut.nablaGl | (intros; apply GlobalTheory.LeviCut.nablaGl <;> assumption)
