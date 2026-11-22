module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LineFacts
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts

@[expose] public section


theorem _root_.GlobalTheory.T.rgExh_lineFacts : CompanionTheory.RgExh.Dec.N.S.LineFacts := by
  first | exact @GlobalTheory.CompanionTheory.GradLine.lineFacts | exact GlobalTheory.CompanionTheory.GradLine.lineFacts | (intros; apply GlobalTheory.CompanionTheory.GradLine.lineFacts <;> assumption)
