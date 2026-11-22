module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHyperplaneVolumeRatioSiegelWeil
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo

@[expose] public section


theorem _root_.GlobalTheory.T.unitary_hyperplane_volumeRatio_siegelWeil : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.RT.MassRatioUnderVolume D := by
  first | exact @GlobalTheory.VolRatioFromSiegelWeil.volumeRatio | exact GlobalTheory.VolRatioFromSiegelWeil.volumeRatio | (intros; apply GlobalTheory.VolRatioFromSiegelWeil.volumeRatio <;> assumption)
