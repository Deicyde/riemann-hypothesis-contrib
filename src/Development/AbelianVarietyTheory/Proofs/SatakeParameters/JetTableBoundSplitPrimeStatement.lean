module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetTableBoundSplitPrime
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb

@[expose] public section


theorem _root_.GlobalTheory.T.jetTableBound_splitPrime : GlobalTheory.AtG.JetSplitAmb := by
  first | exact @GlobalTheory.AtG.jetSplitAmb_holds | exact GlobalTheory.AtG.jetSplitAmb_holds | (intros; apply GlobalTheory.AtG.jetSplitAmb_holds <;> assumption)
