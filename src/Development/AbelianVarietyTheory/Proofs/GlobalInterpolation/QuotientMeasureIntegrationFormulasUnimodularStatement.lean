module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientMeasureIntegrationFormulasUnimodular
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre

@[expose] public section


theorem _root_.GlobalTheory.T.quotientMeasure_integration_formulas_unimodular : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.QuotientMeasures := by
  first | exact @GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quotientMeasures | exact GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quotientMeasures | (intros; apply GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quotientMeasures <;> assumption)
