module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylSchurEndomorphism
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

@[expose] public section

open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_schur_endomorphism : GlobalTheory.LeviCut.NablaSchur := by
  exact @GlobalTheory.LeviCut.nablaSchur
