module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeOfIsNoetherianRing

@[expose] public section


theorem _root_.GlobalTheory.T.isAdicComplete_of_le_of_isNoetherianRing' : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I J : Ideal R), I ≤ J → IsAdicComplete J R → IsAdicComplete I R := by
  first | exact @GlobalTheory.isAdicComplete_of_le_of_isNoetherianRing | exact GlobalTheory.isAdicComplete_of_le_of_isNoetherianRing | (intros; apply GlobalTheory.isAdicComplete_of_le_of_isNoetherianRing <;> assumption)
