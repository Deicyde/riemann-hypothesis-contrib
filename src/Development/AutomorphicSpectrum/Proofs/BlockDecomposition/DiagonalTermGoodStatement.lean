module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalTermGood
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

@[expose] public section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_term_good : DGood := by
  exact @GlobalTheory.CompanionTheory.RgEisDGood.dGood
