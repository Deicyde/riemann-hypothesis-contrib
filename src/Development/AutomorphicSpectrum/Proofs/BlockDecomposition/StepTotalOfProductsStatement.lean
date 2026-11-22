module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StepTotalOfProducts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant

@[expose] public section

open GlobalTheory.CompanionTheory.ThTot

theorem _root_.GlobalTheory.T.step_total_of_products : ProdTh → ProdMeas → StepTotal := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.stepTotal | exact GlobalTheory.CompanionTheory.ThTot.stepTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.stepTotal <;> assumption)
