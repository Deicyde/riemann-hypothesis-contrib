module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InitialStatement
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.InitialStatement : CompanionTheory.RgExh.Dec.N.S.StartOf := by
  exact @GlobalTheory.CompanionTheory.RgStart.startOf
