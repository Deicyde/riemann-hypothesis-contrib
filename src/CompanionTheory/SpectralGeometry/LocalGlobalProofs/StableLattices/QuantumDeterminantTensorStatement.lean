module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantTensor
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

@[expose] public section


theorem _root_.GlobalTheory.T.QuantumDeterminantTensor : CompanionTheory.RgExh.Hk.QdetTens := by
  first | exact @GlobalTheory.CompanionTheory.RgExh.qdetTens | exact GlobalTheory.CompanionTheory.RgExh.qdetTens | (intros; apply GlobalTheory.CompanionTheory.RgExh.qdetTens <;> assumption)
