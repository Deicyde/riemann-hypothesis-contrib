module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistLevelStabiliserAtLevelPrimeProof
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof : GlobalTheory.AdForm.TwLev' := by
  exact @GlobalTheory.AdForm.twLev_prime
