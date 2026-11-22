module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearLatticeCountDescentProof
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.linearLatticeCountDescent_proof : LinearDescent := by
  first | exact @GlobalTheory.UnitLemma.Desc.linearDescent | exact GlobalTheory.UnitLemma.Desc.linearDescent | (intros; apply GlobalTheory.UnitLemma.Desc.linearDescent <;> assumption)
