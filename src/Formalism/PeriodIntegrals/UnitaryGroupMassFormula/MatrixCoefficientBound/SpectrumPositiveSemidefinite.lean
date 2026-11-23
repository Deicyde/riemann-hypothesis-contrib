module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.PermRepApply

@[expose] public section

open Matrix Classical
open scoped ComplexOrder

namespace PI.GGMatBoundW

theorem spectrum_positive_semidefinite : SpecPSD := by
  intro X _ M c hM hev
  have psd (A : Matrix X X ℂ) (hA : A.IsHermitian)
      (h : ∀ (w : X → ℂ) (μ : ℂ), w ≠ 0 → A *ᵥ w = μ • w → ∃ r : ℝ, μ = r ∧ 0 ≤ r) :
      A.PosSemidef := by
    refine hA.posSemidef_iff_eigenvalues_nonneg.mpr fun j => ?_
    have hne := hA.eigenvectorBasis.orthonormal.ne_zero j
    obtain ⟨r, hr, h0⟩ := h _ (hA.eigenvalues j)
      (fun h0 => hne (by ext i; simpa using congrFun h0 i))
      (by rw [hA.mulVec_eigenvectorBasis j]; ext i; simp)
    exact h0.trans (Complex.ofReal_injective hr).ge
  have hN : ((c : ℂ) • (1 : Matrix X X ℂ) - M).IsHermitian :=
    IsHermitian.sub (by simp [IsHermitian, conjTranspose_smul]) hM
  refine ⟨psd M hM fun w μ hw h => ?_, psd _ hN fun w μ hw h => ?_⟩
  · obtain ⟨r, hr, h0, -⟩ := hev w μ hw h
    exact ⟨r, hr, h0⟩
  · obtain ⟨r, hr, -, hrc⟩ := hev w (c - μ) hw <| by
      rw [sub_smul, ← h, sub_mulVec, smul_mulVec, one_mulVec]; abel
    exact ⟨c - r, by push_cast; linear_combination -hr, by linarith⟩

end PI.GGMatBoundW
