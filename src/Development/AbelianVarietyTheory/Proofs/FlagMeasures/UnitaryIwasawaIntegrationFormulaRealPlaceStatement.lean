module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryIwasawaIntegrationFormulaRealPlace
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_iwasawa_integration_formula_real_place : IwasawaFormula := by
  exact @GlobalTheory.FlagMeas.iwasawaFormula
