module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaValueAtOne
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

@[expose] public section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_value_at_one : EpMain → ZetaOne := by
  exact @GlobalTheory.CompanionTheory.EisMG.zetaOne_of_epMain
