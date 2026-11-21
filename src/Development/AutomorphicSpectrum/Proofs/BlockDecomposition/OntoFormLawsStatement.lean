module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OntoFormLaws
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws

@[expose] public section

open CrystallineSemistableComparison.Onto
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.onto_form_laws : CrystallineSemistableComparison.Onto.FormLaws := by
  exact @GlobalTheory.CompanionTheory.OntoForms.formLaws
