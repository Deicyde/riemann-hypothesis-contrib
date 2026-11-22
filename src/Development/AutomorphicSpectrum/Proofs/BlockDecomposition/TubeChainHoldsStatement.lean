module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeChainHolds
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire

@[expose] public section


theorem _root_.GlobalTheory.T.tube_chain_holds : PositivityTheory.RgEis.TubeChain := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.tubeChain | exact GlobalTheory.CompanionTheory.TubeFourier.tubeChain | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.tubeChain <;> assumption)
