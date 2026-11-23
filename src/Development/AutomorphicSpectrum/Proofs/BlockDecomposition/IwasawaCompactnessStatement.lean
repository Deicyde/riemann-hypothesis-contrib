module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCompactness
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant

@[expose] public section

open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_compactness : IwaCpt := by
  exact @GlobalTheory.CompanionTheory.ThTot.iwaCpt
