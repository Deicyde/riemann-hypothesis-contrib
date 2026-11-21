module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerMapsThreePlacesExists
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.AmapsShExists

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wignerMapsThreePlaces_exists : GlobalTheory.WigSh.AmapsShExists := by
  exact @GlobalTheory.WigSh.amapsShExists
