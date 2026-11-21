module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelSplitPlaceCharacterEquivariance
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleUnif

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearModel_splitPlace_characterEquivariance : ∀ D : D7, GlobalTheory.FinPl.LinExact D := by
  exact @GlobalTheory.LinExactAt.linExact
