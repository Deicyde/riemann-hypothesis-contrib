module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorGLBlockIsLocallyConstantCompactSupp
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.unitIndicatorGLBlock_isLocallyConstantCompactSupport : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] (r : ℕ), IsTest (unitG r F) := by
  first | exact @GlobalTheory.JR.UnitTest.unitG_isTest | exact GlobalTheory.JR.UnitTest.unitG_isTest | (intros; apply GlobalTheory.JR.UnitTest.unitG_isTest <;> assumption)
