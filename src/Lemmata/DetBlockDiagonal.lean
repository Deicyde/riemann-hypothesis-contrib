module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

theorem Matrix.det_blockDiagonal' {α : Type*} [Fintype α] [DecidableEq α] {m : α → Type*}
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {R : Type*} [CommRing R]
    (d : ∀ i, Matrix (m i) (m i) R) : (Matrix.blockDiagonal' d).det = ∏ k, (d k).det := by
  classical
  let _ : LinearOrder α := LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective
  rw [(Matrix.blockTriangular_blockDiagonal' d).det_fintype]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  have : (Matrix.blockDiagonal' d).toSquareBlock Sigma.fst k =
      (d k).submatrix (Equiv.sigmaSubtype k) (Equiv.sigmaSubtype k) := by
    ext ⟨⟨i, a⟩, hi⟩ ⟨⟨j, b⟩, hj⟩
    dsimp only at hi hj
    subst hi hj
    simp [Matrix.toSquareBlock_def, Equiv.sigmaSubtype]
  rw [this, Matrix.det_submatrix_equiv_self]
