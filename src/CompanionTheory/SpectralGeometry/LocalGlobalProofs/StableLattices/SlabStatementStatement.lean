module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SlabStatement
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts

@[expose] public section


theorem _root_.GlobalTheory.T.SlabStatement : CompanionTheory.RgExh.Dec.N.S.Slab := by
  first | exact @GlobalTheory.CompanionTheory.SlabLemma.slab | exact GlobalTheory.CompanionTheory.SlabLemma.slab | (intros; apply GlobalTheory.CompanionTheory.SlabLemma.slab <;> assumption)
