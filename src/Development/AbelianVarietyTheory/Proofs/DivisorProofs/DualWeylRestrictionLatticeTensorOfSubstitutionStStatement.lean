module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylRestrictionLatticeTensorOfSubstitutionSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

@[expose] public section

open GlobalTheory.LeviCut

theorem _root_.GlobalTheory.T.dualWeylRestrictionLatticeTensor_of_substitutionStable : GlobalTheory.LeviCut.SubstMem → GlobalTheory.LeviCut.ResLat := by
  first | exact @GlobalTheory.LeviCut.resLat_of_substMem | exact GlobalTheory.LeviCut.resLat_of_substMem | (intros; apply GlobalTheory.LeviCut.resLat_of_substMem <;> assumption)
