module

public import Lib.GLn.SchurModule.LeadingRows
public import TauCeti.Data.Fin.Basic

/-!
# Branching from GL(n+1) to GL(n) × GL(1): the branching vector and the norm bound

This file treats the branching from `GL(n + 1)` to `GL(n) × GL(1)` for the representations of
`∏ τ, GL (N τ)`. The rows `N τ` are the rows `n τ` together with one new row, given by `ι τ`. A
weight `κ` is given by the numbers `κ τ h` of columns of height `h` at the place `τ`. This file
defines the branching vector and writes products of kernels as the minors of one filling. It
proves the norm bound for an equivariant matrix from the fact that the matrix times its adjoint
commutes with the smaller group, so is a scalar.

## Main definitions and results

* `New.GL.branchVector`: the product of the leading minors to the powers `γ`, with the new row
  first, so that every column of positive height contains it, and to the powers `κ`, with the new
  row last, so that no column contains it.
* `New.GL.weylNormSq_mulVec_le_of_equivariant`: the norm bound for an equivariant matrix whose
  transpose sends the extremal vector to a multiple of the branching vector.

Notions from other files:
* `New.MatrixPoly`: Polynomials over `R` in an array of variables `X (a, i)`, with rows `a : m` and
  columns `i : ℕ`.
* `New.rankAt`: The number of elements of the finite row type n_τ at the place τ;
  `New.GL.rowEquivFin n τ : n τ ≃ Fin (rankAt n τ)` is the fixed numbering of these rows, and a
  row's position is its number.
* `New.permArray`: For maps e_τ from rows to natural numbers, the array over R whose entry at row
  (τ,a), column i is 1 if e_τ(a)=i and 0 otherwise.
* `New.toPoly`: The linear map from coordinate vectors ξ to polynomials, ξ ↦ Σ_i (Gξ)_i b_i, with G
  the Gram matrix `New.weylGram` (`New.weylGramOver` is its image over another ring) and b_i the
  basis `New.nablaBasis` of products of minors; `New.GL.nablaCombination` is ξ ↦ Σ_i ξ_i b_i.
* `New.weylEval`: For an array y, the evaluation vector `ev_y` with entries b_i(y); its polynomial
  under `New.toPoly` is `New.weylKernel n κ y`.

## Relation to the literature

Known; see `Lib.GLn.Branching.IntegralMap` for sources.
-/

@[expose] public section

noncomputable section

/-!
## The branching vector and integrality of products of minors

A weight `κ` is given by the numbers `κ τ h` of columns of height `h` at the place `τ`.
`New.weylKernel n κ (permArray e)` is the product over `h < rankAt n τ` of the minors on the first
`h` rows in the order `e` and the first `h` columns, to the powers `κ τ h`; `New.rowSubst z f` is
`y ↦ f (z y)`; `New.toPoly n κ` sends a coordinate vector `ξ` to `∑ i, (G ξ) i • b i`, with `G` the
Gram matrix and `b` the basis of minor products.
-/

section BranchingVector

open Finset Matrix

namespace New.GL

variable {Φ : Type} (R : Type) [CommRing R] [Fintype Φ] {n N : Φ → Type}
  [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, Fintype (N τ)]
  (ι : ∀ τ : Φ, n τ ⊕ Unit ≃ N τ) {κ₀ γ κ' : Φ → ℕ → ℕ}

open scoped Classical in
/-- The numbering of the rows `N τ` by `0, …, rankAt N τ - 1` that gives the added row the number
`i τ` and keeps the rows of `n τ` in their fixed order. -/
def newRowOrder (i : ∀ τ : Φ, Fin (rankAt n τ + 1)) (τ : Φ) : N τ ≃ Fin (rankAt N τ) :=
  -- Insert the new row at position `i τ` into the fixed numbering `rowEquivFin n τ`, then invert.
  finCongr (rankAt_eq_succ ι τ)
    |>.trans (finSuccEquiv' (i τ))
    |>.trans (rowEquivFin n τ).symm.optionCongr
    |>.trans (Equiv.optionEquivSumPUnit (n τ))
    |>.trans (ι τ)
    |>.symm

/-- The product over `τ` and `h < rankAt N τ` of the leading `h × h` minors to the power `γ τ h`
with the added row first, and to the power `κ τ h` with it last. -/
def branchVector (γ κ : Φ → ℕ → ℕ) : MatrixPoly ((τ : Φ) × N τ) R :=
  weylKernel N γ (permArray fun (τ : Φ) (i : N τ) ↦ (newRowOrder ι 0 τ i : ℕ)) *
    weylKernel (R := R) N κ (permArray fun (τ : Φ) (i : N τ) ↦ (newRowOrder ι ⊤ τ i : ℕ))

/-- Multiplying the new row by `s τ` (substituting the matrix `blockScalar ι 1 s`, that is
`diag(1, s τ)` at each `τ`) multiplies `branchVector R ι γ κ'` by the product over `τ` of `s τ` to
the power `diagramWeight (rankAt N) γ (τ, 0)`, the number of columns of `γ` of height
`1, …, rankAt n τ`. -/
lemma rowSubst_branchVector (s : Φ → R) :
    rowSubst (blockScalar ι 1 s) (branchVector R ι γ κ') =
      (∏ τ : Φ, s τ ^ diagramWeight (rankAt N) γ (τ, 0)) • branchVector R ι γ κ' := by
  classical
  -- `blockScalar ι 1 s` is diagonal, so it multiplies each kernel by a power of `s`. The new row is
  -- first in the order for `γ`, so it lies in all columns of positive height; it is last in the
  -- order for `κ'`, so it lies in none.
  have h_triangular (e : ∀ τ : Φ, N τ ≃ Fin (rankAt N τ)) (τ : Φ) :
      (blockScalar (R := R) ι 1 s τ)ᵀ.BlockTriangular (e τ) := by
    have h_diagonal : blockScalar (R := R) ι 1 s τ =
        diagonal (Sum.elim (fun _ : n τ ↦ (1 : R)) (fun _ : Unit ↦ s τ) ∘ (ι τ).symm) := by
      rw [blockScalar, Pi.one_apply, ← diagonal_one, fromBlocks_diagonal, reindex_apply,
        submatrix_diagonal_equiv]
    rw [h_diagonal, diagonal_transpose]
    exact blockTriangular_diagonal _
  rw [branchVector, map_mul, rowSubst_weylKernel_permArray _ _ (h_triangular _),
    rowSubst_weylKernel_permArray _ _ (h_triangular _)]
  simp [newRowOrder, blockScalar, rankAt_eq_succ ι, reindex_equiv (ι _), diagramWeight_apply,
    Nat.Ioo_eq_range']

/-! ### The product of the two kernels as the minors of one filling -/

variable {R} {κ : Φ → ℕ → ℕ}

/-- For numberings `e τ` of the rows, the kernel at the array `permArray e` is the product over `τ`
and `h` of the minor on the first `h` rows in the order `e τ`, to the power `κ τ h`. -/
lemma weylKernel_permArray_eq_prod_minor (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ)) :
    weylKernel n κ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)) =
      ∏ τ : Φ, ∏ h : Fin (rankAt n τ),
        minor R (Sigma.mk τ ∘ (e τ).symm ∘ Fin.castLE h.is_le') ^ κ τ h := by
  classical
  have h_entry (τ : Φ) (h : Fin (rankAt n τ)) (s t : Fin h) :
      ∑ a : n τ, permArray (R := R) (fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)) (⟨τ, a⟩, s) •
          MvPolynomial.X (R := R) ((⟨τ, a⟩ : Σ τ : Φ, n τ), (t : ℕ)) =
        MvPolynomial.X (⟨τ, (e τ).symm (Fin.castLE h.is_le' s)⟩, (t : ℕ)) := by
    have h_iff (a : n τ) : (e τ a : ℕ) = s ↔ a = (e τ).symm (Fin.castLE h.is_le' s) := by
      simp [Equiv.eq_symm_apply, Fin.ext_iff]
    simp [permArray, h_iff, ite_smul]
  simp only [weylKernel, rowSubst_highestPoly, prod_range, h_entry, minor, Function.comp_apply]

omit [Fintype Φ] in
/-- Substituting the permutation matrices of `σ` carries the minor on given rows to the minor on
their images under `σ τ`. -/
lemma rowSubst_permMatrix_minor (σ : ∀ τ : Φ, Equiv.Perm (n τ)) {τ : Φ} {h : ℕ}
    (rows : Fin h → n τ) :
    rowSubst (fun τ : Φ ↦ (σ τ).permMatrix R) (minor R (Sigma.mk τ ∘ rows)) =
      minor R (Sigma.mk τ ∘ σ τ ∘ rows) := by
  rw [minor, minor, AlgHom.map_det]
  refine congrArg det (Matrix.ext fun s t ↦ ?_)
  simp [rowSubst, PEquiv.toMatrix_apply, ite_smul]

/-- The cyclic permutation of `Fin N` that moves `p` to the front and each position below `p` to the
next one; it is the identity if `N ≤ p`. -/
def frontPermutation (N p : ℕ) : Equiv.Perm (Fin N) :=
  if hp : p < N then Fin.cycleRange ⟨p, hp⟩ else 1

/-- For `p < N` the permutation sends a position below `p` to the next one and `p` to `0`, and it
fixes the later positions. -/
lemma frontPermutation_val {N p : ℕ} (hp : p < N) (i : Fin N) :
    (frontPermutation N p i : ℕ) =
      if (i : ℕ) < p then (i : ℕ) + 1 else if (i : ℕ) = p then 0 else (i : ℕ) := by
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, N = M + 1 := ⟨N - 1, by omega⟩
  rw [frontPermutation, dite_eq_left hp]
  split_ifs with h_lt h_eq
  · exact Fin.coe_cycleRange_of_lt h_lt
  · rw [Fin.cycleRange_of_eq (show i = ⟨p, hp⟩ from Fin.ext h_eq), Fin.val_zero]
  · rw [Fin.cycleRange_of_gt (show ⟨p, hp⟩ < i by grind)]

variable (n) in
/-- The renaming of the rows `n τ` that moves the row at position `p τ` to the front and each
earlier row to the next position. -/
def frontRenaming (p : Φ → ℕ) (τ : Φ) : Equiv.Perm (n τ) :=
  (rowEquivFin n τ).symm.permCongr (frontPermutation (rankAt n τ) (p τ))

/-- The rows of column `j` among the columns of height `h`, when the first `k` of these columns hold
the rows at the positions `0, …, h - 1` and the others those at the positions `1, …, h`. -/
def extremalRows {τ : Φ} (k : ℕ) (h : Fin (rankAt n τ)) (j : ℕ) : Fin h → n τ :=
  if j < k then (rowEquivFin n τ).symm ∘ Fin.castLE h.is_le'
  else (rowEquivFin n τ).symm ∘ finRotate (rankAt n τ) ∘ Fin.castLE h.is_le'

/-- Let `κ₀ τ h = κ' τ h + γ τ h` for `0 < h < rankAt n τ`. The product of the kernel of `γ` at the
row order shifted by one and the kernel of `κ'` at the row order `rowEquivFin` is the product, over
the columns of `κ₀`, of the minors on the rows `extremalRows (κ' τ h) h j`. -/
lemma weylKernel_mul_weylKernel_eq_prod_minor
    (hκ₀ : ∀ τ : Φ, ∀ h ∈ Ioo 0 (rankAt n τ), κ₀ τ h = (κ' + γ) τ h) :
    weylKernel n γ (permArray fun (τ : Φ) (a : n τ) ↦
          ((finRotate (rankAt n τ)).symm (rowEquivFin n τ a) : ℕ)) *
        weylKernel n κ' (permArray fun (τ : Φ) (a : n τ) ↦ (rowEquivFin n τ a : ℕ)) =
      ∏ τ : Φ, ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ₀ τ h),
        minor R (Sigma.mk τ ∘ extremalRows (κ' τ h) h j) := by
  -- Both sides are products over `τ` and `h`. For a height `h > 0` the first `κ' τ h` columns
  -- give the minor in the order `rowEquivFin`, and the other `γ τ h` the minor in the shifted
  -- order.
  have h_shift : weylKernel n γ (permArray fun (τ : Φ) (a : n τ) ↦
        ((finRotate (rankAt n τ)).symm (rowEquivFin n τ a) : ℕ)) =
      ∏ τ : Φ, ∏ h : Fin (rankAt n τ), minor R (Sigma.mk τ ∘ (rowEquivFin n τ).symm ∘
        finRotate (rankAt n τ) ∘ Fin.castLE h.is_le') ^ γ τ h :=
    weylKernel_permArray_eq_prod_minor fun τ ↦ (rowEquivFin n τ).trans (finRotate _).symm
  simp only [weylKernel_permArray_eq_prod_minor (rowEquivFin n), h_shift, ← prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ ↦ Finset.prod_congr rfl fun h _ ↦ ?_
  obtain h_zero | h_pos : (h : ℕ) = 0 ∨ 0 < (h : ℕ) := Nat.eq_zero_or_pos h
  · have h_empty : IsEmpty (Fin h) := ⟨fun s ↦ s.pos.ne' h_zero⟩
    simp [minor]
  have h_split : κ₀ τ h = κ' τ h + γ τ h := hκ₀ τ h (mem_Ioo.mpr ⟨h_pos, h.isLt⟩)
  rw [h_split, Fin.prod_univ_add, mul_comm]
  simp [extremalRows]

/-- A filling of the diagram of `κ₀` without its first `p τ` rows, with entries in the last
`rankAt n τ - p τ` rows, numbered from `0`. Among the columns of height `k`, the first
`κ' τ (p τ + k)` hold the rows `0, …, k - 1` and the others the rows `1, …, k`. -/
def extremalFilling (p : Φ → ℕ) (κ₀ κ' : Φ → ℕ → ℕ) :
    ColumnFilling (fun τ : Φ ↦ Fin (rankAt n τ - p τ)) (flatColumns p κ₀) :=
  fun (τ : Φ) (k : Fin (rankAt (fun σ : Φ ↦ Fin (rankAt n σ - p σ)) τ)) (j : Fin (κ₀ τ (p τ + k))) ↦
    if (j : ℕ) < κ' τ (p τ + k) then ⟨Fin.castLE k.is_le', Fin.strictMono_castLE _⟩
    else ⟨fun s : Fin k ↦ ⟨s + 1, by omega⟩, fun _ _ hst ↦ Nat.add_lt_add_right hst 1⟩

omit [Fintype Φ] [∀ τ, DecidableEq (n τ)] in
/-- Put the first `p τ` rows on top of `extremalFilling p κ₀ κ'`. In column `j` of height `h` the
entry of index `s` is then the position `s` if `s < p τ` or `j < κ' τ h`, and `s + 1` otherwise. -/
lemma leadingWedge_extremalFilling {p : Φ → ℕ}
    (h_rank : ∀ τ : Φ, p τ + rankAt (fun σ : Φ ↦ Fin (rankAt n σ - p σ)) τ = rankAt n τ) (τ : Φ)
    (h : Fin (rankAt n τ)) (j : Fin (κ₀ τ h)) (s : Fin h) :
    ((leadingWedge h_rank (extremalFilling p κ₀ κ') τ h j).val s : ℕ) =
      if (s : ℕ) < p τ ∨ (j : ℕ) < κ' τ h then (s : ℕ) else (s : ℕ) + 1 := by
  obtain ⟨h, rfl⟩ : ∃ i : Fin (p τ + rankAt (fun σ : Φ ↦ Fin (rankAt n σ - p σ)) τ),
      Fin.cast (h_rank τ) i = h := ⟨Fin.cast (h_rank τ).symm h, rfl⟩
  induction h using Fin.addCases with
  | left h =>
    rw [ite_eq_left (Or.inl (s.isLt.trans h.isLt))]
    exact leadingWedge_castAdd h_rank _ τ h j s
  | right k =>
    rw [leadingWedge_natAdd h_rank (extremalFilling p κ₀ κ') τ k j]
    induction s using Fin.addCases with
    | left a => simp [Fin.append_left]
    | right a =>
      by_cases hj : (j : ℕ) < κ' τ (p τ + k) <;>
        simp [Fin.append_right, extremalFilling, hj, add_assoc]

omit [Fintype Φ] [∀ τ, DecidableEq (n τ)] in
/-- Let a column of height `h` hold the positions `f s = s` if `s < p τ` or `j < k`, and
`f s = s + 1` otherwise, where `j < k` does not occur for `0 < h ≤ p τ`. After the row at position
`p τ` is moved to the front, its minor is that on `extremalRows k h j` up to sign. -/
lemma exists_minor_extremalRows_eq_smul {τ : Φ} {p : Φ → ℕ} {h : Fin (rankAt n τ)}
    (hp : p τ < rankAt n τ) {j k : ℕ} {f : Fin h → Fin (rankAt n τ)}
    (hf : ∀ s : Fin h, (f s : ℕ) = if (s : ℕ) < p τ ∨ j < k then (s : ℕ) else (s : ℕ) + 1)
    (h_low : 0 < (h : ℕ) → (h : ℕ) ≤ p τ → k ≤ j) :
    ∃ ε : ℤˣ, minor ℤ (Sigma.mk τ ∘ extremalRows k h j) =
      (ε : ℤ) • minor ℤ (Sigma.mk τ ∘ frontRenaming n p τ ∘ (rowEquivFin n τ).symm ∘ f) := by
  obtain h_zero | h_pos : (h : ℕ) = 0 ∨ 0 < (h : ℕ) := Nat.eq_zero_or_pos h
  · have h_empty : IsEmpty (Fin h) := ⟨fun s ↦ s.pos.ne' h_zero⟩
    exact ⟨1, by simp [minor]⟩
  by_cases hj : j < k
  · -- As `p τ < h`, the renaming permutes the first `h` rows among themselves.
    have hp_lt : p τ < h := lt_of_not_ge fun h_le ↦ (h_low h_pos h_le).not_gt hj
    let ρ : Equiv.Perm (Fin h) := (frontPermutation h (p τ)).symm
    have h_rows : extremalRows k h j = (frontRenaming n p τ ∘ (rowEquivFin n τ).symm ∘ f) ∘ ρ := by
      funext s
      obtain ⟨t, rfl⟩ := (frontPermutation h (p τ)).surjective s
      simp [extremalRows, frontRenaming, ρ, Fin.ext_iff, hj, hf, frontPermutation_val hp_lt,
        frontPermutation_val hp]
    refine ⟨Equiv.Perm.sign ρ, ?_⟩
    rw [h_rows, minor, minor, zsmul_eq_mul]
    exact det_permute ρ (of fun s t : Fin h ↦ MvPolynomial.X (R := ℤ)
      ((⟨τ, frontRenaming n p τ ((rowEquivFin n τ).symm (f s))⟩ : Σ σ : Φ, n σ), (t : ℕ)))
  · -- The renaming sends the positions of the column, which omit `p τ`, to `1, …, h` in this order.
    have h_rows : extremalRows k h j = frontRenaming n p τ ∘ (rowEquivFin n τ).symm ∘ f := by
      funext s
      have h_rotate : (finRotate (rankAt n τ) (Fin.castLE h.is_le' s) : ℕ) = s + 1 :=
        Fin.coe_finRotate_of_add_one_lt (show (s : ℕ) + 1 < rankAt n τ by omega)
      have h_front : (frontPermutation (rankAt n τ) (p τ) (f s) : ℕ) = s + 1 := by
        grind [frontPermutation_val]
      simpa [extremalRows, frontRenaming, Fin.ext_iff, hj] using h_rotate.trans h_front.symm
    exact ⟨1, by simp [h_rows]⟩

/-- Let `p τ` be below the number of rows `rankAt n τ` whenever there are rows, and let `h_rank`
say that the first `p τ` rows and the remaining `rankAt n τ - p τ` make up all the rows. Let `κ'`
have no column of height `h` with `0 < h ≤ p τ`, and let `κ₀ τ h = κ' τ h + γ τ h` for
`0 < h < rankAt n τ`. Put the first `p τ` rows on top of `extremalFilling p κ₀ κ'` and move the row
at position `p τ` to the front. Up to sign, the product of minors becomes the product of the kernel
of `γ` at the row order shifted by one and the kernel of `κ'` at the row order `rowEquivFin`. -/
lemma exists_smul_rowSubst_extremalFilling {p : Φ → ℕ}
    (h_rank : ∀ τ : Φ, p τ + rankAt (fun σ : Φ ↦ Fin (rankAt n σ - p σ)) τ = rankAt n τ)
    (hp : ∀ τ : Φ, 0 < rankAt n τ → p τ < rankAt n τ)
    (h_low : ∀ (τ : Φ) (h : ℕ), 0 < h → h ≤ p τ → κ' τ h = 0)
    (hκ₀ : ∀ τ : Φ, ∀ h ∈ Ioo 0 (rankAt n τ), κ₀ τ h = (κ' + γ) τ h) :
    ∃ ε : ℤˣ, (ε : ℤ) • rowSubst (fun τ : Φ ↦ (frontRenaming n p τ).permMatrix ℤ)
        (fillingPoly ℤ (leadingWedge h_rank (extremalFilling p κ₀ κ'))) =
      weylKernel n γ (permArray fun (τ : Φ) (a : n τ) ↦
          ((finRotate (rankAt n τ)).symm (rowEquivFin n τ a) : ℕ)) *
        weylKernel n κ' (permArray fun (τ : Φ) (a : n τ) ↦ (rowEquivFin n τ a : ℕ)) := by
  set T : ColumnFilling n κ₀ := leadingWedge h_rank (extremalFilling p κ₀ κ')
  have h_column : ∀ (τ : Φ) (h : Fin (rankAt n τ)) (j : Fin (κ₀ τ h)), ∃ ε : ℤˣ,
      minor ℤ (Sigma.mk τ ∘ extremalRows (κ' τ h) h j) =
        (ε : ℤ) • minor ℤ (Sigma.mk τ ∘ frontRenaming n p τ ∘ fillingRows T τ h j) :=
    fun τ h j ↦ exists_minor_extremalRows_eq_smul (hp τ h.pos)
      (leadingWedge_extremalFilling h_rank τ h j) fun h_pos h_le ↦ by simp [h_low τ h h_pos h_le]
  choose ε hε using h_column
  have h_subst : rowSubst (fun τ : Φ ↦ (frontRenaming n p τ).permMatrix ℤ) (fillingPoly ℤ T) =
      ∏ τ : Φ, ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ₀ τ h),
        minor ℤ (Sigma.mk τ ∘ frontRenaming n p τ ∘ fillingRows T τ h j) := by
    simp only [fillingPoly, tableauPoly, map_prod, rowSubst_permMatrix_minor]
  refine ⟨∏ τ : Φ, ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ₀ τ h), ε τ h j, ?_⟩
  rw [weylKernel_mul_weylKernel_eq_prod_minor hκ₀, h_subst]
  simp only [hε, zsmul_eq_mul, Units.coe_prod, Int.cast_prod, Finset.prod_mul_distrib]

/-- Let `κ'` have no column of height below `q`, and let `κ₀ τ h = κ' τ h + γ τ h` for
`0 < h < rankAt n τ`. Here `weylKernel n κ y` is the polynomial `f(yᵀx)` in `x`, with `f` the
product of leading minors for `κ`, and `toPoly n κ₀ η` is `Σ_i (Gη)_i b_i` for a Weyl vector `η`
(Gram matrix `G`, basis minor products `b_i`). Then some integer `c` with `0 < c` (a hook number)
satisfies two claims. (a) `c ≤ (L ^ L) ^ 3` for every bound `L` of the number of boxes of `κ₀` in
the columns of height `h` with `q ≤ h < rankAt n τ`. (b) `c` times `weylKernel n γ` at the
permutation array of `rowEquivFin` shifted cyclically by one, times `weylKernel n κ'` at that of
`rowEquivFin`, equals `toPoly n κ₀ η` for some `η : WeylIndexFamily n κ₀ → ℤ`. -/
lemma exists_smul_weylKernel_mul_eq_toPoly [DecidableEq Φ] {q : ℕ}
    (hq : ∀ τ : Φ, ∀ i < q, κ' τ i = 0)
    (hκ₀ : ∀ τ : Φ, ∀ h ∈ Ioo 0 (rankAt n τ), κ₀ τ h = (κ' + γ) τ h) :
    ∃ c : ℤ, 0 < c ∧
      (∀ L : ℕ, ∑ τ : Φ, ∑ h ∈ Ico q (rankAt n τ), h * κ₀ τ h ≤ L → c ≤ (L ^ L) ^ 3) ∧
      ∃ η : WeylIndexFamily n κ₀ → ℤ,
        c • (weylKernel n γ (permArray fun (τ : Φ) (a : n τ) ↦
              ((finRotate (rankAt n τ)).symm (rowEquivFin n τ a) : ℕ)) *
            weylKernel n κ' (permArray fun (τ : Φ) (a : n τ) ↦ (rowEquivFin n τ a : ℕ)) :
              MatrixPoly (Σ τ : Φ, n τ) ℤ) =
          toPoly n κ₀ η := by
  -- Let `p` be `q - 1`, capped at the last position. Every column of height above `p` contains the
  -- rows at the positions `1, …, p`, and a column of height `h ≤ p` holds those at `1, …, h`. Up to
  -- a renaming of the rows and a sign, the product is thus that of a filling with `p` leading rows,
  -- and the hook number `c` of the diagram without its first `p` rows makes `c` times that product
  -- the image of an integral vector.
  let p : Φ → ℕ := fun τ ↦ min (q - 1) (rankAt n τ - 1)
  have h_rank (τ : Φ) : p τ + rankAt (fun σ : Φ ↦ Fin (rankAt n σ - p σ)) τ = rankAt n τ := by
    simp [rankAt, p]
  have hp (τ : Φ) (h_pos : 0 < rankAt n τ) : p τ < rankAt n τ := by grind
  have h_low (τ : Φ) (h : ℕ) (h_pos : 0 < h) (h_le : h ≤ p τ) : κ' τ h = 0 := hq τ h (by grind)
  let c : ℤ := hookNumber (flatColumns p κ₀) (rankAt fun τ : Φ ↦ Fin (rankAt n τ - p τ))
  obtain ⟨η, hη⟩ : ∃ η : WeylIndexFamily n κ₀ → ℤ,
      toPoly n κ₀ η = c • fillingPoly ℤ (leadingWedge h_rank (extremalFilling p κ₀ κ')) :=
    exists_toPoly_eq_hookNumber_smul_leadingWedge h_rank _
  obtain ⟨ε, hε⟩ := exists_smul_rowSubst_extremalFilling h_rank hp h_low hκ₀
  -- The Schur matrix of the transposed permutation matrices acts as the renaming of the rows.
  let P (τ : Φ) : Matrix (n τ) (n τ) ℤ := (frontRenaming n p τ).permMatrix ℤ
  have h_rename :
      toPoly n κ₀ (schur κ₀ (fun τ : Φ ↦ (P τ)ᵀ) *ᵥ η) = rowSubst P (toPoly n κ₀ η) := by
    simp [toPoly_schur FitsRanks.refl, detPow]
  refine ⟨c, hookNumber_pos, fun L hL ↦ ?_, (ε : ℤ) • schur κ₀ (fun τ : Φ ↦ (P τ)ᵀ) *ᵥ η, ?_⟩
  · -- A column of height `h ≥ p τ` leaves `h - p τ` boxes below the first `p τ` rows, which is
    -- `0` if `h < q`.
    have h_boxes (τ : Φ) :
        ∑ h ∈ range (rankAt (fun σ : Φ ↦ Fin (rankAt n σ - p σ)) τ), h * flatColumns p κ₀ τ h ≤
          ∑ h ∈ Ico q (rankAt n τ), h * κ₀ τ h :=
      calc
        _ = ∑ h ∈ Ico (p τ) (rankAt n τ), (h - p τ) * κ₀ τ h := by
          simp [sum_Ico_eq_sum_range, flatColumns, rankAt]
        _ ≤ ∑ h ∈ Ico q (rankAt n τ), (h - p τ) * κ₀ τ h := by
          refine sum_le_sum_of_ne_zero fun h h_mem h_ne ↦ ?_
          have h_above : h - p τ ≠ 0 := left_ne_zero_of_mul h_ne
          grind
        _ ≤ ∑ h ∈ Ico q (rankAt n τ), h * κ₀ τ h := by
          gcongr
          exact Nat.sub_le _ _
    exact hookNumber_le ((sum_le_sum fun τ _ ↦ h_boxes τ).trans hL)
  · rw [map_smul, h_rename, hη, map_smul, smul_comm (ε : ℤ) c, hε]

end New.GL

end BranchingVector

/-!
## The norm of a branching map

Let `T` be the matrix of a branching map over `ℂ` and `C` its adjoint for the forms of the two
matrices `weylGramOver`. By equivariance `T * C` commutes with every `schur κ₀ g`, so it is a scalar
(`New.mem_range_scalar_of_commute_schur`). This scalar is the squared norm of the image under `C`
of the evaluation vector at the permutation array, and the hypothesis on the top vector bounds it.
The norm bound follows from the inequality `New.GL.posDef_cauchy_schwarz`.
-/

section NormBound

open Matrix ComplexOrder

namespace New.GL

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ] {n N : Φ → Type} [∀ τ : Φ, Fintype (n τ)]
  [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, Fintype (N τ)] [∀ τ : Φ, DecidableEq (N τ)]
  (ι : ∀ τ : Φ, n τ ⊕ Unit ≃ N τ) {κ₀ γ κ' : Φ → ℕ → ℕ}

/-- Let `B` be an integral matrix with
`B * schur (γ + κ') (diag(g, 1)) = (∏ τ, det (g τ) ^ κ' τ (rankAt n τ)) • (schur κ₀ g * B)`
for all complex `g`, with `diag(g, 1)` built by `blockScalar ι`. Let `v` be the Gram matrix
`weylGramOver` times `weylEval` at the permutation array of `rowEquivFin`, and assume also that the
row vector `v ᵥ* B` has the polynomial `c • branchVector ℂ ι γ κ'` under `nablaCombination`
(ξ ↦ Σ ξ_i b_i over the basis products of minors). Then
`weylNormSq (B *ᵥ ξ) ≤ c ^ 2 * weylNormSq ξ` for every complex vector `ξ`. -/
lemma weylNormSq_mulVec_le_of_equivariant {c : ℤ}
    {B : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily N (γ + κ')) ℤ}
    (B_top : nablaCombination (γ + κ') ((weylGramOver *ᵥ weylEval n κ₀
        (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) ᵥ*
          B.map (Int.cast : ℤ → ℂ)) =
      (c : ℂ) • branchVector ℂ ι γ κ')
    (B_block : ∀ g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ,
      B.map (Int.cast : ℤ → ℂ) * schur (γ + κ') (blockScalar ι g 1) =
        (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (schur κ₀ g * B.map (Int.cast : ℤ → ℂ)))
    (ξ : WeylIndexFamily N (γ + κ') → ℂ) :
    weylNormSq (B.map (Int.cast : ℤ → ℂ) *ᵥ ξ) ≤ (c : ℝ) ^ 2 * weylNormSq ξ := by
  -- Let `G₀`, `G` be the two matrices `weylGramOver` and `T` the matrix `B` over `ℂ`. The adjoint
  -- `C` of `T` for their forms is given by `G * C = Tᵀ * G₀`. By equivariance `T * C` commutes with
  -- every `schur κ₀ g`, so it is a scalar `m`. Then `‖C x‖² = m ‖x‖²`, and `m = ‖C v‖² ≤ c ^ 2` for
  -- the evaluation vector `v` of norm 1. The inequality `posDef_cauchy_schwarz` for `ξ` and
  -- `C (T ξ)` gives the bound.
  obtain ⟨T, hT⟩ : ∃ T : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily N (γ + κ')) ℂ,
      T = B.map (Int.cast : ℤ → ℂ) := ⟨_, rfl⟩
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily n κ₀) ℂ,
      G₀ = weylGramOver := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : Matrix (WeylIndexFamily N (γ + κ')) (WeylIndexFamily N (γ + κ')) ℂ,
      G = weylGramOver := ⟨_, rfl⟩
  simp only [← hT] at B_block ⊢
  rw [← hT, ← hG₀] at B_top
  have hT_real : Tᴴ = Tᵀ := by
    rw [hT]
    ext i j
    simp
  have hG_posDef : G.PosDef := hG ▸ weylGramOver_posDef
  have hG₀_herm : G₀ᴴ = G₀ := by rw [hG₀, weylGramOver_posDef.isHermitian.eq]
  have hG_det : IsUnit G.det := (isUnit_iff_isUnit_det G).1 hG_posDef.isUnit
  have h_coe (x : WeylIndexFamily N (γ + κ') → ℂ) : (weylNormSq x : ℂ) = star x ⬝ᵥ G *ᵥ x := by
    rw [hG, coe_weylNormSq]
  have h_coe₀ (x : WeylIndexFamily n κ₀ → ℂ) : (weylNormSq x : ℂ) = star x ⬝ᵥ G₀ *ᵥ x := by
    rw [hG₀, coe_weylNormSq]
  obtain ⟨C, hGC⟩ : ∃ C : Matrix (WeylIndexFamily N (γ + κ')) (WeylIndexFamily n κ₀) ℂ,
      G * C = Tᵀ * G₀ :=
    ⟨G⁻¹ * (Tᵀ * G₀), mul_nonsing_inv_cancel_left _ _ hG_det⟩
  have hCG : Cᴴ * G = G₀ * T := by
    have h := congrArg conjTranspose hGC
    rwa [← hT_real, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      hG_posDef.isHermitian.eq, hG₀_herm] at h
  -- `schur (γ + κ') (diag(g, 1)) * C = det • (C * schur κ₀ g)`: the adjoint of the equivariance.
  have h_adj (g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ) :
      schur (γ + κ') (blockScalar ι g 1) * C =
        (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (C * schur κ₀ g) := by
    have h_tr : (fun τ : Φ ↦ (blockScalar ι g 1 τ)ᵀ) = blockScalar ι (fun τ : Φ ↦ (g τ)ᵀ) 1 := by
      funext τ
      simp [blockScalar, fromBlocks_transpose]
    have h_cancel : G * (schur (γ + κ') (blockScalar ι g 1) * C) =
        G * ((∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (C * schur κ₀ g)) := by
      calc G * (schur (γ + κ') (blockScalar ι g 1) * C)
        _ = (T * schur (γ + κ') (blockScalar ι (fun τ : Φ ↦ (g τ)ᵀ) 1))ᵀ * G₀ := by
          rw [← Matrix.mul_assoc, hG, weylGramOver_mul_schur, ← hG, h_tr, Matrix.mul_assoc, hGC,
            ← Matrix.mul_assoc, transpose_mul]
        _ = (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (Tᵀ * (G₀ * schur κ₀ g)) := by
          rw [B_block, hG₀, weylGramOver_mul_schur]
          simp only [transpose_smul, transpose_mul, Matrix.smul_mul, Matrix.mul_assoc,
            det_transpose]
        _ = G * ((∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (C * schur κ₀ g)) := by
          rw [← Matrix.mul_assoc, ← hGC, Matrix.mul_smul, Matrix.mul_assoc]
    calc schur (γ + κ') (blockScalar ι g 1) * C
      _ = G⁻¹ * (G * (schur (γ + κ') (blockScalar ι g 1) * C)) :=
        (nonsing_inv_mul_cancel_left _ _ hG_det).symm
      _ = (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (C * schur κ₀ g) := by
        rw [h_cancel, nonsing_inv_mul_cancel_left _ _ hG_det]
  obtain ⟨m, hm⟩ := mem_range_scalar_of_commute_schur (T := T * C) fun g hg ↦ by
    have h_det : (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun τ _ ↦ pow_ne_zero _ (det_ne_zero_of_left_inverse (hg τ))
    have h_left : T * ((∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (C * schur κ₀ g)) =
        (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (schur κ₀ g * T) * C := by
      rw [← h_adj g, ← Matrix.mul_assoc, B_block]
    have h_smul : (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (T * C * schur κ₀ g) =
        (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (schur κ₀ g * (T * C)) := by
      rw [Matrix.mul_assoc T C, ← Matrix.mul_smul T, h_left, Matrix.smul_mul, Matrix.mul_assoc]
    exact smul_right_injective _ h_det h_smul
  have hTC : T * C = m • (1 : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily n κ₀) ℂ) := by
    rw [← hm, scalar_apply, smul_one_eq_diagonal]
  have h_CGC : Cᴴ * (G * C) = m • G₀ := by
    rw [← Matrix.mul_assoc, hCG, Matrix.mul_assoc, hTC, Matrix.mul_smul, Matrix.mul_one]
  have h_C (x : WeylIndexFamily n κ₀ → ℂ) : (weylNormSq (C *ᵥ x) : ℂ) = m * weylNormSq x := by
    rw [h_coe, h_coe₀, star_mulVec_dotProduct]
    simp only [mulVec_mulVec, h_CGC, smul_mulVec, dotProduct_smul, smul_eq_mul]
  -- The scalar is the squared norm of `C v`, which is at most `c ^ 2`.
  have h_toPoly : toPoly N (γ + κ') (C *ᵥ weylEval n κ₀
        (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) =
      toPoly N γ ((c : ℂ) • weylEval N γ
          (permArray fun (τ : Φ) (i : N τ) ↦ (newRowOrder ι 0 τ i : ℕ))) *
        toPoly N κ' (weylEval N κ'
          (permArray fun (τ : Φ) (i : N τ) ↦ (newRowOrder ι ⊤ τ i : ℕ))) := by
    rw [map_smul, toPoly_weylEval, toPoly_weylEval, ← nablaCombination_weylGramOver_mulVec, ← hG,
      mulVec_mulVec, hGC, ← mulVec_mulVec, mulVec_transpose, B_top, branchVector, smul_mul_assoc]
  have h_m : (m : ℂ) = (weylNormSq (C *ᵥ weylEval n κ₀
      (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) : ℝ) := by
    rw [h_C, weylNormSq_weylEval_permArray (rowEquivFin n), Complex.ofReal_one, mul_one]
  have h_m_le : weylNormSq (C *ᵥ weylEval n κ₀
      (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) ≤ (c : ℝ) ^ 2 := by
    refine (weylNormSq_le_mul_of_toPoly_eq h_toPoly).trans_eq ?_
    rw [weylNormSq_smul, weylNormSq_weylEval_permArray (newRowOrder ι 0),
      weylNormSq_weylEval_permArray (newRowOrder ι ⊤), mul_one, mul_one, Complex.norm_intCast,
      sq_abs]
  -- The pairing of `ξ` and `C (T ξ)` is `‖T ξ‖²`.
  have h_GCT : G * (C * T) = Tᵀ * (G₀ * T) := by
    rw [← Matrix.mul_assoc, hGC, Matrix.mul_assoc]
  have h_pair : star ξ ⬝ᵥ G *ᵥ (C *ᵥ (T *ᵥ ξ)) = (weylNormSq (T *ᵥ ξ) : ℂ) := by
    rw [h_coe₀, star_mulVec_dotProduct, hT_real]
    simp only [mulVec_mulVec, h_GCT]
  have h_norm : weylNormSq (C *ᵥ (T *ᵥ ξ)) = weylNormSq (C *ᵥ weylEval n κ₀
      (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) * weylNormSq (T *ᵥ ξ) := by
    have h := h_C (T *ᵥ ξ)
    rw [h_m] at h
    exact_mod_cast h
  have h_cs : weylNormSq (T *ᵥ ξ) ^ 2 ≤ weylNormSq (C *ᵥ (T *ᵥ ξ)) * weylNormSq ξ := by
    have h := posDef_cauchy_schwarz hG_posDef ξ (C *ᵥ (T *ᵥ ξ))
    rwa [h_pair, ← h_coe, ← h_coe, Complex.ofReal_re, Complex.ofReal_re, Complex.norm_real,
      Real.norm_eq_abs, sq_abs] at h
  rcases (weylNormSq_nonneg (T *ᵥ ξ)).eq_or_lt with h_zero | h_pos
  · rw [← h_zero]
    exact mul_nonneg (sq_nonneg _) (weylNormSq_nonneg ξ)
  · refine le_trans (le_of_mul_le_mul_right ?_ h_pos)
      (mul_le_mul_of_nonneg_right h_m_le (weylNormSq_nonneg ξ))
    rw [h_norm] at h_cs
    linarith

end New.GL

end NormBound

end
