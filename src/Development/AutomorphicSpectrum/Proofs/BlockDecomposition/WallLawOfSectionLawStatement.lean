module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WallLawOfSectionLaw
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wall_law_of_section_law : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.WallLaw := by
  exact @GlobalTheory.CompanionTheory.RgEis.wallLaw_of_secLaw
