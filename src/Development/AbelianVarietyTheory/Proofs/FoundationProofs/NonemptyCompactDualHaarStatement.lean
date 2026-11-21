module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_compactDualHaar : Nonempty CDHaar := by
  exact @GlobalTheory.CompactDualExists.nonempty_cdHaar
