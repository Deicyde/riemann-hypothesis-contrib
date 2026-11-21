module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckeLBoundedInVerticalStrips
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedHeckeL_bounded_in_vertical_strips : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips := by
  exact @GlobalTheory.HeckeStrip.completedLBoundedInStrips
