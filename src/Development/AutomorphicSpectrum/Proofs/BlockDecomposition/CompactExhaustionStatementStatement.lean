module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactExhaustionStatement
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

@[expose] public section


theorem _root_.GlobalTheory.T.compact_exhaustion_statement : PositivityTheory.RgDs.K.Exhaust := by
  first | exact @GlobalTheory.CompanionTheory.WordFam.exhaust | exact GlobalTheory.CompanionTheory.WordFam.exhaust | (intros; apply GlobalTheory.CompanionTheory.WordFam.exhaust <;> assumption)
