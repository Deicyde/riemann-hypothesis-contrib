module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactExhaustionStatement
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_exhaustion_statement : PositivityTheory.RgDs.K.Exhaust := by
  exact @GlobalTheory.CompanionTheory.WordFam.exhaust
