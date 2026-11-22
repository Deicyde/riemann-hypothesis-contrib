module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActionEquivarianceStatement
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

@[expose] public section


theorem _root_.GlobalTheory.T.action_equivariance_statement : PositivityTheory.RgDs.K.ActEquiv := by
  first | exact @GlobalTheory.CompanionTheory.ActEquivK.actEquiv | exact GlobalTheory.CompanionTheory.ActEquivK.actEquiv | (intros; apply GlobalTheory.CompanionTheory.ActEquivK.actEquiv <;> assumption)
