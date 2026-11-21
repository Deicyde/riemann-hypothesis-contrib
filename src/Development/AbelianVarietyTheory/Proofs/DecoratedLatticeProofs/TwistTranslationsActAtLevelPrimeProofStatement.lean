module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistTranslationsActAtLevelPrimeProof
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistTranslationsActAtLevelPrime_proof : GlobalTheory.AdForm.TwTrans' := by
  exact @GlobalTheory.AdForm.TransAct.twTransAct
