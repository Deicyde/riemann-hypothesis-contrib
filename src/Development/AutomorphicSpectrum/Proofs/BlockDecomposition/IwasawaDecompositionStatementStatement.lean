module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif

@[expose] public section

open GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomposition_statement : GlobalTheory.CompanionTheory.Jp.JpIw := by
  exact @GlobalTheory.CompanionTheory.Jp.Iw.jpIw
