module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

@[expose] public section

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lcsc_adelic_unitary_group : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), LocallyCompactSpace (HA (AF F) σ J) ∧ SecondCountableTopology (HA (AF F) σ J) ∧ T2Space (HA (AF F) σ J) := by
  exact @GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary
