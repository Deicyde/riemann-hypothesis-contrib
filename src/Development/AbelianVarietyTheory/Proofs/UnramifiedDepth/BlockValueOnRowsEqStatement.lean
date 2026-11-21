module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BlockValueOnRowsEq
public import Formalism.LocalToGlobal.CharacterGerms.BiadditiveInSingleVariables

@[expose] public section

open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockValue_on_rows_eq : BiValue := by
  exact @GlobalTheory.blockValue_rows
