module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PrincipalSum
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.PrincipalSum : CompanionTheory.RgExh.Hk.PrinSum := by
  exact @GlobalTheory.CompanionTheory.PrinSumP.prinSum
