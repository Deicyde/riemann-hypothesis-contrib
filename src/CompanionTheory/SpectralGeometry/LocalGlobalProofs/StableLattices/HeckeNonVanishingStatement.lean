module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeNonVanishing
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HeckeNonVanishing : CompanionTheory.RgExh.Hk.NonVan := by
  exact @GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof.nonVan
