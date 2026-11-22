module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BlockValueOnRowsEq
public import Formalism.LocalToGlobal.CharacterGerms.BiadditiveInSingleVariables

@[expose] public section

open Formalism.L2.FormalSeriesBounds

theorem _root_.GlobalTheory.T.blockValue_on_rows_eq : BiValue := by
  first | exact @GlobalTheory.blockValue_rows | exact GlobalTheory.blockValue_rows | (intros; apply GlobalTheory.blockValue_rows <;> assumption)
