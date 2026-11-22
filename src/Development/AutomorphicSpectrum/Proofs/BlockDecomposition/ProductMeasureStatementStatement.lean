module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductMeasureStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant

@[expose] public section

open GlobalTheory.CompanionTheory.ThTot

theorem _root_.GlobalTheory.T.product_measure_statement : ProdMeas := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.ProdMeasPf.prodMeas | exact GlobalTheory.CompanionTheory.ThTot.ProdMeasPf.prodMeas | (intros; apply GlobalTheory.CompanionTheory.ThTot.ProdMeasPf.prodMeas <;> assumption)
