module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeChainHolds
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tube_chain_holds : PositivityTheory.RgEis.TubeChain := by
  exact @GlobalTheory.CompanionTheory.TubeFourier.tubeChain
