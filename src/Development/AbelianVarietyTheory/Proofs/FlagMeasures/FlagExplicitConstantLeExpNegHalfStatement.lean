module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagExplicitConstantLeExpNegHalf
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_explicit_constant_le_exp_neg_half : ConstantBound := by
  exact @GlobalTheory.FlagMeas.constantBound
