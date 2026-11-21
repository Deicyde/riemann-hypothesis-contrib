module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastFrameCoeffRingNotDvd
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs

@[expose] public section

open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_natCast_frameCoeffRing_not_dvd : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (N : ℕ) (F : Frame l ι N), F.Ok → ∀ n : ℕ, ¬ l ∣ n → IsUnit (n : F.O) := by
  exact @GlobalTheory.ExpFrame.Frame.isUnit_natCast_of_not_dvd
