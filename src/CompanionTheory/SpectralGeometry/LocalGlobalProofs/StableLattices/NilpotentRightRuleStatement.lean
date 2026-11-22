module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentRightRule
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.RightRule

@[expose] public section


theorem _root_.GlobalTheory.T.NilpotentRightRule : CompanionTheory.RgExh.Dec.N.RightRule := by
  first | exact @GlobalTheory.CompanionTheory.RightRule.rightRule | exact GlobalTheory.CompanionTheory.RightRule.rightRule | (intros; apply GlobalTheory.CompanionTheory.RightRule.rightRule <;> assumption)
