module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialPolynomialSolutionSpaceFiniteDimensio
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemExpSolCons

@[expose] public section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponentialPolynomialSolutionSpace_finiteDimensional : ∀ l : List ℂ, FiniteDimensional ℂ (expSol l) := by
  exact @GlobalTheory.HCF.expSol_finiteDimensional
