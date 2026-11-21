module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StepTotalOfProducts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant

@[expose] public section

open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_total_of_products : ProdTh → ProdMeas → StepTotal := by
  exact @GlobalTheory.CompanionTheory.ThTot.stepTotal
