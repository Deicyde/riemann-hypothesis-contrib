module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviDecompOfBlockDet
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_decomp_of_block_det : PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.LeviS := by
  exact @GlobalTheory.CompanionTheory.RgEisLevi.leviS
