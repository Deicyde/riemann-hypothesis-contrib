module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemIntegralSurjectivityOfOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm

@[expose] public section

open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveSystemIntegralSurjectivity_of_one : ∀ N : ℕ, 1 ≤ N → GLOnto 1 → GLOnto N := by
  exact @GlobalTheory.PMonE.glOnto_of_one
