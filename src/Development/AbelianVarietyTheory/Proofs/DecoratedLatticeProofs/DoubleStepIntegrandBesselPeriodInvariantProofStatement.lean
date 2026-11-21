module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandBesselPeriodInvariantProof
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleUnif

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStepIntegrandBesselPeriodInvariant_proof : ∀ D : D7, GlobalTheory.FinPl.HandInv D := by
  exact @GlobalTheory.FinPl.HandInvPf.handInv
