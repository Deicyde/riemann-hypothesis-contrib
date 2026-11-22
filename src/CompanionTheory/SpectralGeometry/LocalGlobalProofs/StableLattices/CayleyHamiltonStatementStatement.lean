module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CayleyHamiltonStatement
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

@[expose] public section


theorem _root_.GlobalTheory.T.CayleyHamiltonHk : CompanionTheory.RgExh.Hk.CayleyHam := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.cayleyHam | exact GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.cayleyHam | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.cayleyHam <;> assumption)
