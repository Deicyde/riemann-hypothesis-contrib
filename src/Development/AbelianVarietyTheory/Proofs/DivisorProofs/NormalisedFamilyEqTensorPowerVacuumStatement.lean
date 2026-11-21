module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyEqTensorPowerVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedFamily_eq_tensorPower_vacuum : GlobalTheory.ColNorms.FamilyTie := by
  exact @GlobalTheory.FamilyTieProof.familyTie
