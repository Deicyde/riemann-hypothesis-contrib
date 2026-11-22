module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollifierApproximationHilbert
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt

@[expose] public section


theorem _root_.GlobalTheory.T.mollifier_approximation_hilbert : PositivityTheory.RgDs.Hilb.StepMoll := by
  first | exact @GlobalTheory.CompanionTheory.HilbMoll.stepMoll | exact GlobalTheory.CompanionTheory.HilbMoll.stepMoll | (intros; apply GlobalTheory.CompanionTheory.HilbMoll.stepMoll <;> assumption)
