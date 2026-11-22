module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FlatMvPowerSeriesOfIsNoetherianRing

@[expose] public section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.module_flat_mvPowerSeries_of_isNoetherianRing : ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (σ : Type), Module.Flat T (MvPowerSeries σ T) := by
  first | exact @GlobalTheory.FiniteHeight.flat_mvPowerSeries_of_isNoetherianRing | exact GlobalTheory.FiniteHeight.flat_mvPowerSeries_of_isNoetherianRing | (intros; apply GlobalTheory.FiniteHeight.flat_mvPowerSeries_of_isNoetherianRing <;> assumption)
