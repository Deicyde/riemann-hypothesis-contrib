module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeOperatorsActOnRamifiedColumns
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrime_operators_act_on_ramified_columns : GlobalTheory.AdForm.TwS' := by
  exact @GlobalTheory.AdForm.TwSProof.twS
