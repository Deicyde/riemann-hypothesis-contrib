module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianVolumeDependsOnlyOnFieldSignature
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_volume_depends_only_on_field_signature : VolumeInvariant := by
  exact @GlobalTheory.VolInvariant.volumeInvariant
