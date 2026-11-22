module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationQuadraticFieldExists
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.weilRepresentation_quadraticField_exists : WeilField := by
  first | exact @GlobalTheory.JR.WeilQuad.weilField_main | exact GlobalTheory.JR.WeilQuad.weilField_main | (intros; apply GlobalTheory.JR.WeilQuad.weilField_main <;> assumption)
