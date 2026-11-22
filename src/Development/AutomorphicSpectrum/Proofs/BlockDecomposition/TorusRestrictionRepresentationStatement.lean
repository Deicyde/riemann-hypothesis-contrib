module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusRestrictionRepresentation
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

@[expose] public section


theorem _root_.GlobalTheory.T.torus_restriction_representation : PositivityTheory.RgDs.K.RhoTorus := by
  first | exact @GlobalTheory.CompanionTheory.RgTorus.rhoTorus | exact GlobalTheory.CompanionTheory.RgTorus.rhoTorus | (intros; apply GlobalTheory.CompanionTheory.RgTorus.rhoTorus <;> assumption)
