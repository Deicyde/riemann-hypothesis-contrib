module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermAbsoluteVolumeBoundOfVolumeRatioInduction
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermAbsoluteVolumeBound_of_volume_ratio_induction : VolumeStep → AbsoluteVolume := by
  exact @GlobalTheory.FlagMeas.AbsVol.absoluteVolume_of_volumeStep
