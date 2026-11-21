module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LipschitzFormulaTotallyRealPoisson
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceDualDifferent

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lipschitz_formula_totally_real_poisson : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz := by
  exact @GlobalTheory.LipschitzTR.lipschitz
