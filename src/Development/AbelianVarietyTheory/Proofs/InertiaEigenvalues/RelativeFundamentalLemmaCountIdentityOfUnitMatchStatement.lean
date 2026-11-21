module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeFundamentalLemmaCountIdentityOfUnitMatch
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch

@[expose] public section

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relativeFundamentalLemmaCountIdentity_of_unitMatch : (∀ r : ℕ, GlobalTheory.JR.UnitMatch r) → CountIdentity := by
  exact @GlobalTheory.CountId.countIdentity_of_unitMatch
