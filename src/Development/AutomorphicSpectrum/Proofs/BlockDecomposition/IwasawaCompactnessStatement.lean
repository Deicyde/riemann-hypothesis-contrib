module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCompactness
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant

@[expose] public section

open GlobalTheory.CompanionTheory.ThTot

theorem _root_.GlobalTheory.T.iwasawa_compactness : IwaCpt := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.iwaCpt | exact GlobalTheory.CompanionTheory.ThTot.iwaCpt | (intros; apply GlobalTheory.CompanionTheory.ThTot.iwaCpt <;> assumption)
