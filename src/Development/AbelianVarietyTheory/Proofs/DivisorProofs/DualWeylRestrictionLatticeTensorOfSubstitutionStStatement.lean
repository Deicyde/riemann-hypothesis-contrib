module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylRestrictionLatticeTensorOfSubstitutionSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

@[expose] public section

open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylRestrictionLatticeTensor_of_substitutionStable : GlobalTheory.LeviCut.SubstMem → GlobalTheory.LeviCut.ResLat := by
  exact @GlobalTheory.LeviCut.resLat_of_substMem
