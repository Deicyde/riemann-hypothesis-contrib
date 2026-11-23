module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StagedEstimateHolds
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.staged_estimate_holds : PositivityTheory.RgEis.PiLocalization₂ := by
  exact @GlobalTheory.CompanionTheory.RgEis.stage
