module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ParabolicSubgroupEquality
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts

@[expose] public section


theorem _root_.GlobalTheory.T.ParabolicSubgroupEquality : CompanionTheory.RgExh.Dec.N.S.PSubEq := by
  first | exact @GlobalTheory.CompanionTheory.PSubFlag.psubEq | exact GlobalTheory.CompanionTheory.PSubFlag.psubEq | (intros; apply GlobalTheory.CompanionTheory.PSubFlag.psubEq <;> assumption)
