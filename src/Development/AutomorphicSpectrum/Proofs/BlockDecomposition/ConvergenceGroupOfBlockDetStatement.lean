module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceGroupOfBlockDet
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergence_group_of_block_det : PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.ConvGrOf := by
  exact @GlobalTheory.CompanionTheory.Plucker.convGrOf
