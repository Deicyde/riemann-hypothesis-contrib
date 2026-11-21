module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneFgLatticeEqFractionalIdealSmulVector
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Dets

@[expose] public section

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankOne_fg_lattice_eq_fractionalIdeal_smul_vector : ∀ {K : Type} [Field K] [NumberField K] {m : ℕ} (ell : Submodule (𝓞 K) (Fin m → K)),
    ReciprocityTheory.GeometryOfNumbersTheory.latRank K ell = 1 → ell.FG →
    ∃ v : Fin m → K, v ≠ 0 ∧ ∃ 𝔟 : Submodule (𝓞 K) K, 𝔟.FG ∧ 𝔟 ≠ ⊥ ∧
      ∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v := by
  exact @GlobalTheory.latRank_one_eq_ideal_smul
