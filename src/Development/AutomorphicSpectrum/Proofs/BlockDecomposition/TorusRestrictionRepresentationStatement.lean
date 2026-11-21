module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusRestrictionRepresentation
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_restriction_representation : PositivityTheory.RgDs.K.RhoTorus := by
  exact @GlobalTheory.CompanionTheory.RgTorus.rhoTorus
