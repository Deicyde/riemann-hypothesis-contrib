module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalBoundProductOverPlacesLabel
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC

@[expose] public section


theorem _root_.GlobalTheory.T.localBound_productOverPlaces_label : GlobalTheory.TypeAsm.ProdC := by
  first | exact @GlobalTheory.TypeAsm.prodC_holds | exact GlobalTheory.TypeAsm.prodC_holds | (intros; apply GlobalTheory.TypeAsm.prodC_holds <;> assumption)
