module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.PermRepApply

@[expose] public section

open Matrix Classical Formalism.L2.SG.GGMirabolic
open scoped ComplexOrder

namespace PI.GGMatBoundW

theorem ggMatrixBoundOfLit_of (hM : MatrixEq) (hH : TotHerm) (hE : EigBound) (hS : SpecPSD)
    (hCL : ConvScalarOfLit) (hRB : GenericRatioOfBound) (hCU : CardUni) : GGMatrixBoundOfLit := by
  intro hGG hMB ι _ Fq _ _ k ψ hψ hq X _ _ hfree d hd
  obtain ⟨hA, hAt⟩ := hM ι Fq k ψ X hfree d hd
  have hspec := hS X _ _ (hH ι Fq k ψ X) fun w μ hw hAw =>
    hE (hCL hGG) (hRB hMB hCU) ι Fq k ψ hψ hq (X → ℂ) (permRep _ X) w μ hw
      (by rw [← hAw, ← toLin'_apply, toLin'_toMatrix'])
  rw [hAt, hA]
  exact ⟨hspec.1.transpose, hspec.2⟩

end PI.GGMatBoundW
