module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif

@[expose] public section

open GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_bound_statement : GlobalTheory.CompanionTheory.Jp.JpHgt := by
  exact @GlobalTheory.CompanionTheory.Jp.Hgt.jpHgt
