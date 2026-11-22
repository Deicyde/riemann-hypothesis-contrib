module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InitialStatement
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts

@[expose] public section


theorem _root_.GlobalTheory.T.InitialStatement : CompanionTheory.RgExh.Dec.N.S.StartOf := by
  first | exact @GlobalTheory.CompanionTheory.RgStart.startOf | exact GlobalTheory.CompanionTheory.RgStart.startOf | (intros; apply GlobalTheory.CompanionTheory.RgStart.startOf <;> assumption)
