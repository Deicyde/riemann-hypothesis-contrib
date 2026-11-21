module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVSmul
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

@[expose] public section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lines_decomposition : Lines := by
  exact @GlobalTheory.CompanionTheory.RgEisLines.lines
