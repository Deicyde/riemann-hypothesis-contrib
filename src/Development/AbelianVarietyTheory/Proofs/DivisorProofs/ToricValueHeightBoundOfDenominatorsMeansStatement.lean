module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricValueHeightBoundOfDenominatorsMeans
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds

@[expose] public section

open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricValueHeightBound_of_denominatorsMeans : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → FieldDat → TorEx → DenEx → DenSum → BetaArch → ThbSt := by
  exact @GlobalTheory.SqTop.thbSt_of_inputs
