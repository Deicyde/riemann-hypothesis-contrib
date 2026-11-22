module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicFunctionFacts
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

@[expose] public section


theorem _root_.GlobalTheory.T.holomorphic_function_facts : PositivityTheory.RgDs.K.HolFacts := by
  first | exact @GlobalTheory.CompanionTheory.HolOm.holFacts | exact GlobalTheory.CompanionTheory.HolOm.holFacts | (intros; apply GlobalTheory.CompanionTheory.HolOm.holFacts <;> assumption)
