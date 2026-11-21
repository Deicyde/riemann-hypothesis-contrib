module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetIndicatorThetaRefinementProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetIndicatorThetaRefinement_proof : GlobalTheory.ColNorms.CosetRefinement := by
  exact @GlobalTheory.ColNorms.coset_refinement
