module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeBackwardStable
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

@[expose] public section


theorem _root_.GlobalTheory.T.HeckeBackwardStable : CompanionTheory.RgExh.Hk.BackStable := by
  first | exact @GlobalTheory.CompanionTheory.RgHeckeBack.backStable | exact GlobalTheory.CompanionTheory.RgHeckeBack.backStable | (intros; apply GlobalTheory.CompanionTheory.RgHeckeBack.backStable <;> assumption)
