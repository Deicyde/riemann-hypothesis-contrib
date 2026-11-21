module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GalleryOfTubesAndCrossing
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gallery_of_tubes_and_crossing : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.IdTube → PositivityTheory.RgEis.TubeChain → PositivityTheory.RgEis.Cross → PositivityTheory.RgEis.Gallery := by
  exact @GlobalTheory.CompanionTheory.RgEisGal.gallery
