module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianVolumeDependsOnlyOnFieldSignature
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.hermitian_volume_depends_only_on_field_signature : VolumeInvariant := by
  first | exact @GlobalTheory.VolInvariant.volumeInvariant | exact GlobalTheory.VolInvariant.volumeInvariant | (intros; apply GlobalTheory.VolInvariant.volumeInvariant <;> assumption)
