module

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.SimpleRing.Principal
public import Lib.General.LinearAlgebra.MatricesNearIdentity
import Lib.DiscreteSeries.FlenstedJensen.CasimirEigenfunction
import Lib.DiscreteSeries.Holomorphic.HighestVectorExtension
import Lib.DiscreteSeries.Holomorphic.MaximalCompactMinors

/-!
# One minor near the identity

For a unitary matrix `k` and a diagonal projection `P`, the principal minor of `k` on the range of
`P` has squared modulus at most `exp (-‖[P, k]‖² / 2)` (`norm_principalMinor_sq_le_exp`).

For `g` in `USign ε` near `1` and `X = g - 1`, the coefficient `l.dsCoeff g` is
`l.flenstedJensen 1 y` for a matrix `y = (1 - u) g (1 - v)` with `u`, `v` strictly triangular, and
each principal minor of `kᴴ y k` on a set of lowest entries of `l` is
`exp (tr (P logOneAdd X) + ‖[P, X]‖² / 4 + r)` with an explicit bound for `r`
(`exists_principalMinor_eq_exp`). This rests on an exact formula for `det (1 + P X)` through
`logOneAdd` (`exists_det_compress_eq_exp_logOneAdd`). The norm of a matrix is the entrywise `ℓ²`
norm (`Norms.Frobenius`).
-/

@[expose] public section

noncomputable section

section SizeOfOneMinor

open Matrix Finset Norms.Frobenius Complex

namespace New.DiscreteSeries

variable {n : Type} [Fintype n] [DecidableEq n] {P k : Matrix n n ℂ} {p : n → Prop}
  [DecidablePred p]

/-! ### The size of one minor -/

/-- The square of `|det Y|` is at most `exp (tr (Yᴴ Y - 1))`; this trace is real. -/
lemma norm_det_sq_le_exp (Y : Matrix n n ℂ) :
    ‖Y.det‖ ^ 2 ≤ Real.exp (Yᴴ * Y - 1).trace.re := by
  -- Use `x ≤ exp (x - 1)` on the eigenvalues `x ≥ 0` of `Yᴴ Y`.
  have hY : (Yᴴ * Y).IsHermitian := isHermitian_conjTranspose_mul_self Y
  have nonneg : ∀ i, 0 ≤ hY.eigenvalues i := eigenvalues_conjTranspose_mul_self_nonneg Y
  have trace_eq : (Yᴴ * Y - 1).trace.re = ∑ i, (hY.eigenvalues i - 1) := by
    rw [trace_sub, hY.trace_eq_sum_eigenvalues]
    simp
  calc ‖Y.det‖ ^ 2 = ‖(Yᴴ * Y).det‖ := by
        rw [det_mul, det_conjTranspose, norm_mul, norm_star, sq]
    _ = ∏ i, hY.eigenvalues i := by
        simp [hY.det_eq_prod_eigenvalues, abs_of_nonneg (nonneg _)]
    _ ≤ ∏ i, Real.exp (hY.eigenvalues i - 1) :=
        prod_le_prod₀ (fun i _ ↦ nonneg i) fun i _ ↦ by
          linarith only [Real.add_one_le_exp (hY.eigenvalues i - 1)]
    _ = Real.exp (Yᴴ * Y - 1).trace.re := by rw [trace_eq, Real.exp_sum]

/-- The principal minor of `X` on the indices satisfying `p` is `det (1 + P (X - 1))`, where `P` is
the diagonal projection to these indices. -/
lemma principalMinor_eq_det_coordProj (X : Matrix n n ℂ) (p : n → Prop) [DecidablePred p] :
    principalMinor X p = (1 + coordProj p * (X - 1)).det := by
  rw [principalMinor_eq_det, coordProj, sub_eq_add_neg, ← mul_neg, neg_sub]

/-- For a unitary matrix `k` and an orthogonal projection `P`, the crossing block
`M = (1 - P) k P` satisfies `Mᴴ M = P - P kᴴ P k P`. -/
lemma conjTranspose_mul_self_one_sub_mul_mul (hP : IsStarProjection P) (hk : kᴴ * k = 1) :
    ((1 - P) * k * P)ᴴ * ((1 - P) * k * P) = P - P * kᴴ * P * k * P := by
  have hPP : P * P = P := hP.isIdempotentElem
  have hP_adj : Pᴴ = P := hP.isSelfAdjoint
  simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hP_adj]
  linear_combination (norm := noncomm_ring) P * kᴴ * hPP * k * P + P * hk * P + hPP

/-- For a unitary matrix `k` and an orthogonal projection `P`, the Frobenius norms of the
commutator and of the block `(1 - P) k P` satisfy `‖[P, k]‖² = 2 ‖(1 - P) k P‖²`. -/
lemma norm_lie_sq_of_unitary (hP : IsStarProjection P) (hk : kᴴ * k = 1) :
    ‖⁅P, k⁆‖ ^ 2 = 2 * ‖(1 - P) * k * P‖ ^ 2 := by
  have hk' : k * kᴴ = 1 := mul_eq_one_symm hk
  have hPP : P * P = P := hP.isIdempotentElem
  have hP_adj : Pᴴ = P := hP.isSelfAdjoint
  -- Both sides are `2 (tr P - tr (P kᴴ P k))`.
  have lie_eq : ⁅P, k⁆ᴴ * ⁅P, k⁆ = kᴴ * (P * k) - kᴴ * (P * k * P) - P * kᴴ * P * k + P := by
    rw [Ring.lie_def, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hP_adj]
    linear_combination (norm := noncomm_ring) kᴴ * hPP * k + P * hk * P + hPP
  have trace_conj : (kᴴ * (P * k)).trace = P.trace := by
    rw [trace_mul_comm, mul_assoc, hk', mul_one]
  have trace_left : (kᴴ * (P * k * P)).trace = (P * kᴴ * P * k).trace := by
    simp only [← mul_assoc, trace_mul_comm _ P]
  have trace_right : (P * kᴴ * P * k * P).trace = (P * kᴴ * P * k).trace := by
    simp only [trace_mul_comm _ P, ← mul_assoc, hPP]
  have block_eq : ((1 - P) * k * P)ᴴ * ((1 - P) * k * P) = P - P * kᴴ * P * k * P :=
    conjTranspose_mul_self_one_sub_mul_mul hP hk
  rw [← ofReal_inj, ofReal_mul, ← trace_star_mul_self_eq_norm_sq,
    ← trace_star_mul_self_eq_norm_sq, lie_eq, block_eq]
  simp only [trace_add, trace_sub, trace_conj, trace_left, trace_right, ofReal_ofNat]
  ring

/-- Size of one minor: let `k` be a unitary matrix, `S` the set of indices satisfying `p`, and
`P = coordProj p` the diagonal projection to `S`. Then the principal minor of `k` on `S` satisfies
`|det_S k|² ≤ exp (-‖[P, k]‖² / 2)`. -/
theorem norm_principalMinor_sq_le_exp (p : n → Prop) [DecidablePred p] (hk : kᴴ * k = 1) :
    ‖principalMinor k p‖ ^ 2 ≤ Real.exp (-(‖⁅coordProj p, k⁆‖ ^ 2 / 2)) := by
  -- With `M = (1 - P) k P` and `Y = (1 - P) + P k P` we have `det_S k = det Y` and
  -- `Yᴴ Y = (1 - P) + P kᴴ P k P = 1 - Mᴴ M`, while `‖[P, k]‖² = 2 ‖M‖²`.
  have hP : IsStarProjection (coordProj p) := isStarProjection_coordProj p
  set P : Matrix n n ℂ := coordProj p
  have hPP : P * P = P := hP.isIdempotentElem
  let M : Matrix n n ℂ := (1 - P) * k * P
  let Y : Matrix n n ℂ := 1 - P + P * k * P
  have minor_eq : principalMinor k p = Y.det := by
    have Y_eq : Y = 1 + P * (k - 1) * P := by
      simp [Y, mul_sub, sub_mul, hPP, sub_add_eq_add_sub, add_sub_assoc]
    rw [principalMinor_eq_det_coordProj, Y_eq, det_one_add_mul_comm (P * (k - 1)), ← mul_assoc, hPP]
  have Y_sq : Yᴴ * Y = 1 - P + P * kᴴ * P * k * P := by
    simp [Y, hP.isSelfAdjoint.star_eq, ← star_eq_conjTranspose, add_mul, mul_add, mul_sub, sub_mul,
      ← mul_assoc, mul_assoc _ P P, hPP]
  have gram_eq : Yᴴ * Y - 1 = -(Mᴴ * M) := by
    rw [Y_sq, conjTranspose_mul_self_one_sub_mul_mul hP hk]
    abel
  calc ‖principalMinor k p‖ ^ 2 ≤ Real.exp (Yᴴ * Y - 1).trace.re := by
        rw [minor_eq]
        exact norm_det_sq_le_exp Y
    _ = Real.exp (-‖M‖ ^ 2) := by
        rw [gram_eq, trace_neg, trace_star_mul_self_eq_norm_sq, neg_re, ofReal_re]
    _ = Real.exp (-(‖⁅P, k⁆‖ ^ 2 / 2)) := by
        rw [norm_lie_sq_of_unitary hP hk, mul_div_cancel_left₀ _ two_ne_zero]

/-- The entry `(i, j)` of the commutator of `X` with the diagonal projection to the indices
satisfying `p` has the norm of `X i j` if exactly one of `p i`, `p j` holds, else it is `0`. -/
lemma norm_lie_coordProj_apply (X : Matrix n n ℂ) (i j : n) :
    ‖⁅coordProj p, X⁆ i j‖ = if p i ↔ p j then 0 else ‖X i j‖ := by
  by_cases hi : p i <;> by_cases hj : p j <;> simp [coordProj, Ring.lie_def, hi, hj]

end New.DiscreteSeries

end SizeOfOneMinor

section DeterminantOfCompression

open Ring Matrix Norms.Frobenius Complex intervalIntegral

namespace New.DiscreteSeries

variable {n : Type*} [Fintype n] [DecidableEq n] {P Q X Y : Matrix n n ℂ} {δ c : ℝ}

attribute [local simp] mul_add add_mul mul_assoc lie_def IsIdempotentElem.eq
  IsIdempotentElem.mul_self_mul IsStarProjection.isIdempotentElem

/-- Let `P` and `Q` be orthogonal projections, and let `‖X‖ ≤ δ ≤ 1 / 2`, `tr ([P, Q] Y) = 0`,
`‖[P, X] - Y‖ ≤ δ c`, `‖Y‖ ≤ c` and `‖Q - P‖ ≤ c`. Then
`det (1 + P X) = exp (tr (Q logOneAdd X) - tr (Y ^ 2) / 4 + r)` with `|r| ≤ 100 δ c ^ 2`. -/
lemma exists_det_compress_eq_exp_logOneAdd (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hδ : δ ≤ 2⁻¹) (hX : ‖X‖ ≤ δ) (h_comm : (⁅P, Q⁆ * Y).trace = 0)
    (h_near : ‖⁅P, X⁆ - Y‖ ≤ δ * c) (hY : ‖Y‖ ≤ c) (hPQ : ‖Q - P‖ ≤ c) :
    ∃ r : ℂ, (1 + P * X).det = cexp ((Q * logOneAdd X).trace - 4⁻¹ * (Y * Y).trace + r) ∧
      ‖r‖ ≤ 100 * δ * c ^ 2 := by
  have hδ_nonneg : 0 ≤ δ := (norm_nonneg X).trans hX
  have hc_nonneg : 0 ≤ c := (norm_nonneg Y).trans hY
  have hPX : ‖P * X‖ ≤ δ := norm_proj_mul_le hP hX
  have h_lie : ‖⁅P, X⁆‖ ≤ c + 2⁻¹ * c := (norm_le_insert' _ Y).trans (by grw [hY, h_near, hδ])
  -- `log det (1 + P X)` is the integral over `[0, 1]` of `tr ((1 + s P X)⁻¹ P X)`, by
  -- `det_one_add_eq_exp_trace_logOneAdd`, and `tr (Q logOneAdd X)` is that of
  -- `tr (Q (1 + s X)⁻¹ X)`. So the remainder `r` is the integral of the difference, corrected by
  -- `s tr (Y ^ 2) / 2`.
  have h_int_P := intervalIntegrable_trace_mul_inv_one_add_smul_mul (hPX.trans hδ) 1
  have h_int_Q := intervalIntegrable_trace_mul_inv_one_add_smul_mul (hX.trans hδ) Q
  have h_int_Y : IntervalIntegrable (fun s : ℝ ↦ (s : ℂ) * (2⁻¹ * (Y * Y).trace))
      MeasureTheory.volume 0 1 :=
    (continuous_ofReal.intervalIntegrable ..).mul_const _
  have h_integral : ∫ s : ℝ in 0..1, ((1 * ((1 + s • (P * X))⁻¹ * (P * X))).trace -
        (Q * ((1 + s • X)⁻¹ * X)).trace + s * (2⁻¹ * (Y * Y).trace)) =
      (logOneAdd (P * X)).trace - (Q * logOneAdd X).trace + 4⁻¹ * (Y * Y).trace := by
    rw [integral_add (h_int_P.sub h_int_Q) h_int_Y, integral_sub h_int_P h_int_Q,
      integral_trace_mul_inv_one_add_smul_mul (hPX.trans hδ) 1,
      integral_trace_mul_inv_one_add_smul_mul (hX.trans hδ) Q, integral_mul_const,
      integral_ofReal, integral_id]
    norm_num
    ring
  refine ⟨(logOneAdd (P * X)).trace - (Q * logOneAdd X).trace + 4⁻¹ * (Y * Y).trace, ?_, ?_⟩
  · rw [det_one_add_eq_exp_trace_logOneAdd (hPX.trans hδ)]
    congr 1
    ring
  -- It remains to bound the integrand at each `s ∈ (0, 1]`.
  rw [← h_integral]
  refine (norm_integral_le_of_norm_le_const (C := 100 * δ * c ^ 2) fun s hs ↦ ?_).trans_eq
    (by simp)
  have hs_mem : s ∈ Set.Icc (0 : ℝ) 1 := by grind
  have hs_half : s / 2 ∈ Set.Icc (0 : ℝ) 1 := by grind
  -- The resolvents `W = (1 + s X)⁻¹` and `V = (1 + s P X)⁻¹` are within `2 δ` of `1`.
  have hsX : ‖s • X‖ ≤ δ := norm_smul_le_of_le_one s hX hs_mem
  have hsPX : ‖s • (P * X)‖ ≤ δ := norm_smul_le_of_le_one s hPX hs_mem
  have hW_mul : (1 + s • X) * (1 + s • X)⁻¹ = 1 :=
    one_add_mul_inv_one_add (hsX.trans_lt (by linarith))
  have hW_mul' : (1 + s • X)⁻¹ * (1 + s • X) = 1 :=
    inv_one_add_mul_one_add (hsX.trans_lt (by linarith))
  have hW : ‖(1 + s • X)⁻¹ - 1‖ ≤ 2 * δ :=
    (norm_inv_one_add_sub_one_le (hsX.trans hδ)).trans (by linarith)
  have hV_mul : (1 + s • (P * X)) * (1 + s • (P * X))⁻¹ = 1 :=
    one_add_mul_inv_one_add (hsPX.trans_lt (by linarith))
  have hV_mul' : (1 + s • (P * X))⁻¹ * (1 + s • (P * X)) = 1 :=
    inv_one_add_mul_one_add (hsPX.trans_lt (by linarith))
  have hV : ‖(1 + s • (P * X))⁻¹ - 1‖ ≤ 2 * δ :=
    (norm_inv_one_add_sub_one_le (hsPX.trans hδ)).trans (by linarith)
  set W : Matrix n n ℂ := (1 + s • X)⁻¹
  set V : Matrix n n ℂ := (1 + s • (P * X))⁻¹
  set A : Matrix n n ℂ := ⁅P, X⁆
  set D : Matrix n n ℂ := Q - P
  let Z : Matrix n n ℂ := W - 1
  let N : Matrix n n ℂ := Z * (A * Z + A) + A * Z
  -- Rewrite the integrand as four traces, each of a product with one factor of size `δ` and two
  -- of size `c`. The identity uses `W (1 + s X) = 1`, `V (1 + s P X) = 1`, `P ^ 2 = P`,
  -- `Q ^ 2 = Q`, `tr ([P, Q] Y) = 0` and `tr (M M') = tr (M' M)`.
  have h_split : (1 * (V * (P * X))).trace - (Q * (W * X)).trace + s * (2⁻¹ * (Y * Y).trace) =
      trace ((P * D + Q * D - D) * (A - Y + Z * A - s • (N + A) * X)) -
        trace (s • (P * A) * ((N + A) * (V - 1) + N)) -
        trace ((D - P * D - P * D) * D * (X + Z * X)) -
        trace ((s / 2) • (A - Y) * (A + Y)) := by
    linear_combination (norm := (
      simp +zetaDelta only [hP, hQ, trace_mul_comm P, trace_mul_comm V, trace_mul_comm Y (_ * _),
        trace_mul_comm X (P * X), mul_sub, sub_mul, mul_add, add_mul, mul_assoc, one_mul, mul_one,
        lie_def, IsStarProjection.isIdempotentElem, IsIdempotentElem.eq,
        IsIdempotentElem.mul_self_mul, trace_sub, trace_add, trace_smul, smul_add,
        Algebra.smul_mul_assoc, Algebra.mul_smul_comm, real_smul, ofReal_div, ofReal_ofNat]
      ring_nf))
      h_comm + congr(($hV_mul' * P * W * X * P +
        V * P * (A * ($hW_mul' * P * (1 - W) + W * P * $hW_mul) - $hW_mul * X * P) +
        (1 - P) * $hV_mul * P * X - ⁅P, D⁆ * ($hW_mul' * P * W - W * P * $hW_mul) * X).trace)
  rw [h_split]
  apply le_trans
  · apply_rules (transparency := .reducible) (maxDepth := 99)
      [norm_smul_le_of_le_one s (hρ := hs_mem), norm_smul_le_of_le_one (s / 2) (hρ := hs_half),
      norm_proj_mul_le hP, norm_proj_mul_le hQ, @norm_trace_mul_le, norm_sub_le_of_le,
      norm_add_le_of_le, norm_mul_le_of_le]
  · have hδc := mul_nonneg hδ_nonneg (sq_nonneg c)
    linarith [mul_le_mul_of_nonneg_right hδ hδc,
      mul_le_mul_of_nonneg_right hδ (mul_nonneg hδ_nonneg hδc)]

end New.DiscreteSeries

end DeterminantOfCompression

section MinorExpansion

open Ring Matrix Norms.Frobenius Complex ComplexConjugate

namespace New.DiscreteSeries

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} {h : ℕ} {l : HCParam ε}
  {X : Matrix n n ℂ}

attribute [local simp] mul_add add_mul mul_assoc lie_def principalMinor_eq_det coordProj

/-- The determinant of a matrix that is triangular for an injective order `o` is the product of
its diagonal entries. -/
lemma det_eq_prod_diag_of_blockTriangular {b : Matrix n n ℂ} {o : n → ℤ} (ho : o.Injective) :
    b.BlockTriangular o → b.det = ∏ i, b i i :=
  let := LinearOrder.lift' o ho
  det_of_isUpperTriangular

/-- The value of `l.flenstedJensen 1` at `zᴴ` is the conjugate of its value at `z`. -/
lemma conj_flenstedJensen_one (z : Matrix n n ℂ) :
    conj (l.flenstedJensen 1 z) = l.flenstedJensen 1 zᴴ := by
  simp [flenstedJensen, conj_weightMinors, ← integral_conj, mul_comm, mul_assoc]

/-- Let `u` be block diagonal and strictly triangular: `u i j = 0` unless `l i < l j` and
`ε i = ε j`. If `X` and `(1 - u) * X` are accretive, then `l.flenstedJensen 1` at
`((1 - u) * X)ᴴ` is the conjugate of its value at `X`. -/
lemma flenstedJensen_shift_eq_conj (hl : l.HasGap h) {u : Matrix n n ℂ}
    (hu : ∀ i j, ¬(l i < l j ∧ ε i = ε j) → u i j = 0) (hX : X.IsAccretive)
    (huX : ((1 - u) * X).IsAccretive) :
    l.flenstedJensen 1 ((1 - u) * X)ᴴ = conj (l.flenstedJensen 1 X) := by
  have h_det : (1 - u).det ≠ 0 ∧ X.det ≠ 0 := by simpa [det_mul] using huX.det_ne_zero
  -- `1 - u` is block diagonal and triangular, with diagonal entries `1`.
  have hu_mem : 1 - u ∈ blockDiagAlg ε := mem_blockDiagAlg.2 fun i j hij ↦ by
    simp [one_apply_ne (show i ≠ j by rintro rfl; exact hij rfl), hu i j (by tauto)]
  have hu_borel : IsBorelMatrix (-(-l)) (1 - u) := ⟨fun i j hij ↦ by
    have h_lt : l j < l i := by simpa using hij
    simp [one_apply_ne (show i ≠ j by rintro rfl; exact lt_irrefl _ h_lt),
      hu i j fun h' ↦ lt_asymm h_lt h'.1], h_det.1⟩
  -- Move the factor `1 - u` from the second argument to the first, where it acts by a character
  -- with value `1`.
  have h_move : l.flenstedJensen (1 - u) X = l.flenstedJensen 1 ((1 - u) * X) := by
    have := flenstedJensen_eq_of_accretive hl (one_mem _) (by simpa using huX) hu_mem
      (g := (1 - u) * X) (by simp_all)
    simp_all
  have h_char : l.flenstedJensen (1 - u) X = l.flenstedJensen 1 X := by
    have h_minors (k : maxCompactU ε) :
        weightMinors l.lowestKType ((1 - u) * (k : Matrix n n ℂ)) =
          weightMinors l.lowestKType (k : Matrix n n ℂ) := by
      rw [hl.isKDominant_lowestKType.weightMinors_oppBorel_mul hl.neg.injective
        ((Matrix.isUnit_iff_isUnit_det _).1 k.val.val.isUnit).ne_zero hu_mem hu_borel]
      simp [diagChar, show ∀ i, u i i = 0 from fun i ↦ hu i i (by simp)]
    simp [flenstedJensen, h_minors]
  rw [← conj_flenstedJensen_one, ← h_move, h_char]

/-- Multiplying `g` on the left by `1 - u` and on the right by `1 - r`, where `‖u‖` and `‖r‖` are at
most `‖g - 1‖ < 1 / 1000`, keeps it within `4 ‖g - 1‖` of `1`. -/
lemma norm_one_sub_mul_mul_one_sub_sub_one_le {g u r : Matrix n n ℂ} (hg : ‖g - 1‖ < 1000⁻¹)
    (hu : ‖u‖ ≤ ‖g - 1‖) (hr : ‖r‖ ≤ ‖g - 1‖) : ‖(1 - u) * g * (1 - r) - 1‖ ≤ 4 * ‖g - 1‖ := by
  set X : Matrix n n ℂ := g - 1
  have hX_nonneg : 0 ≤ ‖X‖ := norm_nonneg X
  -- With `m = X - u - u X`, the matrix is `1 + m - r - m r`.
  let m : Matrix n n ℂ := X - u - u * X
  have hm : ‖m‖ ≤ ‖X‖ + ‖X‖ + ‖X‖ * ‖X‖ :=
    norm_sub_le_of_le (norm_sub_le_of_le (le_refl ‖X‖) hu) (norm_mul_le_of_le hu le_rfl)
  have h_eq : (1 - u) * g * (1 - r) - 1 = m - r - m * r := by
    have hgX : g = 1 + X := by simp [X]
    simp only [m, hgX]
    noncomm_ring
  rw [h_eq]
  have := norm_sub_le_of_le (norm_sub_le_of_le hm hr) (norm_mul_le_of_le hm hr)
  nlinarith [mul_le_mul_of_nonneg_right hg.le hX_nonneg,
    mul_le_mul_of_nonneg_right hg.le (mul_nonneg hX_nonneg hX_nonneg)]

/-- Let `u` and `r` be block diagonal and strictly triangular in opposite directions: `u i j = 0`
unless `l i < l j` and `ε i = ε j`, and `r i j = 0` unless `l j < l i` and `ε i = ε j`. If `g`,
`(1 - u) g` and `(1 - u) g (1 - r)` are accretive, then the coefficient `l.dsCoeff g` is
`l.flenstedJensen 1` at `(1 - u) g (1 - r)`: removing either factor conjugates the value. -/
lemma dsCoeff_eq_flenstedJensen_one_sub_mul_mul_one_sub (hl : l.HasGap h) {g : USign ε}
    {u r : Matrix n n ℂ} (hu : ∀ i j, ¬(l i < l j ∧ ε i = ε j) → u i j = 0)
    (hr : ∀ i j, ¬(l j < l i ∧ ε i = ε j) → r i j = 0) (hg : (g : Matrix n n ℂ).IsAccretive)
    (hug : ((1 - u) * (g : Matrix n n ℂ)).IsAccretive)
    (hy : ((1 - u) * (g : Matrix n n ℂ) * (1 - r)).IsAccretive) :
    l.dsCoeff g = l.flenstedJensen 1 ((1 - u) * g * (1 - r)) := by
  have h_left := flenstedJensen_shift_eq_conj hl hu hg hug
  have h_right := flenstedJensen_shift_eq_conj hl (u := rᴴ)
    (X := ((1 - u) * (g : Matrix n n ℂ))ᴴ) (fun i j hij ↦ by
      simp [hr j i fun h ↦ hij ⟨h.1, h.2.symm⟩])
    (by simpa [IsAccretive, add_comm] using hug)
    (by simpa [IsAccretive, add_comm] using hy)
  rw [dsCoeff_eq_flenstedJensen hl (one_mem _) (by simpa using hg)]
  simpa using (h_right.trans (congrArg _ h_left)).symm

/-- On a set `p` of highest entries of `l`, unipotent factors `1 - u` and `1 - r`, as in
`dsCoeff_eq_flenstedJensen_one_sub_mul_mul_one_sub`, do not change the principal minor. -/
lemma principalMinor_one_sub_mul_mul_one_sub (hl : l.HasGap h) {g u r : Matrix n n ℂ}
    (hu : ∀ i j, ¬(l i < l j ∧ ε i = ε j) → u i j = 0)
    (hr : ∀ i j, ¬(l j < l i ∧ ε i = ε j) → r i j = 0) {p : n → Prop} [DecidablePred p]
    (hp : ∀ i j, p i → ¬p j → l j < l i) :
    principalMinor ((1 - u) * g * (1 - r)) p = principalMinor g p := by
  have hu_diag (i : n) : u i i = 0 := hu i i (by simp)
  have hr_diag (i : n) : r i i = 0 := hr i i (by simp)
  rw [principalMinor_mul, principalMinor_mul, principalMinor_eq_det,
    det_eq_prod_diag_of_blockTriangular hl.injective, mul_comm, principalMinor_eq_det,
    det_eq_prod_diag_of_blockTriangular hl.neg.injective] <;>
    simp [BlockTriangular, Matrix.one_apply, hu_diag, hr_diag] <;> grind

/-- Taking the commutator with the coordinate projection `coordProj p` commutes with keeping some
entries of a matrix and putting `0` elsewhere (`entryMask`). -/
lemma lie_coordProj_entryMask (p : n → Prop) [DecidablePred p] (rel : n → n → Prop)
    [DecidableRel rel] (X : Matrix n n ℂ) :
    ⁅coordProj p, entryMask rel X⁆ = entryMask rel ⁅coordProj p, X⁆ := by
  ext i j
  simp [diagonal_mul, mul_diagonal]
  grind

/-- Keeping some entries of a matrix does not increase the norm of its commutator with the
coordinate projection `coordProj p`. -/
lemma norm_lie_coordProj_entryMask_le (p : n → Prop) [DecidablePred p] (rel : n → n → Prop)
    [DecidableRel rel] (X : Matrix n n ℂ) :
    ‖⁅coordProj p, entryMask rel X⁆‖ ≤ ‖⁅coordProj p, X⁆‖ := by
  rw [lie_coordProj_entryMask]
  exact norm_entryMask_le

/-- Let `p` be a set of lowest entries of `l`. The commutator `[coordProj p, X]` vanishes at the
entries `(i, j)` with `l i = l j`, so its block diagonal part is the sum of its parts strictly below
the diagonal for the orders `-l` and `l`. -/
private lemma blockDiagPart_lie_coordProj {p : n → Prop} [DecidablePred p]
    (hp : ∀ i j, p i → ¬p j → l i < l j) (X : Matrix n n ℂ) :
    blockDiagPart ε ⁅coordProj p, X⁆ =
      lowerMask ε (-l) ⁅coordProj p, X⁆ + lowerMask ε l ⁅coordProj p, X⁆ := by
  ext i j
  simp [blockDiagPart, diagonal_mul, mul_diagonal]
  grind

/-- The principal minor of `x` on the complement of `p` is `det (1 + (1 - coordProj p) (x - 1))`. -/
lemma det_one_add_one_sub_coordProj_mul_sub_one (p : n → Prop) [DecidablePred p]
    (x : Matrix n n ℂ) : (1 + (1 - coordProj p) * (x - 1)).det = principalMinor x (¬p ·) := by
  -- `1 - coordProj p` is the coordinate projection onto the complement of `p`.
  have h_compl : 1 - coordProj p = diagonal fun i ↦ if ¬p i then (1 : ℂ) else 0 := by
    rw [coordProj, ← diagonal_one, diagonal_sub]
    congr 1
    ext i
    by_cases hp : p i <;> simp [hp]
  rw [principalMinor_eq_det, ← h_compl]
  congr 1
  noncomm_ring

/-- For `kᴴ k = 1`, the principal minor of `kᴴ y k` on `p` is `det (1 + Q (y - 1))`, where
`Q = k P kᴴ` is the conjugate of the projection `P = coordProj p`. -/
lemma principalMinor_conjTranspose_mul_mul {k : Matrix n n ℂ} (hk : kᴴ * k = 1)
    (y : Matrix n n ℂ) (p : n → Prop) [DecidablePred p] :
    principalMinor (kᴴ * y * k) p = (1 + k * coordProj p * kᴴ * (y - 1)).det := by
  simp only [mul_assoc, principalMinor_eq_det, coordProj, det_one_add_mul_comm k]
  noncomm_ring [hk]

/-- For `Pᴴ = P` and a unitary `k`, the conjugate `k P kᴴ` is within `‖[P, k]‖` of `P`. -/
lemma norm_sub_mul_mul_conjTranspose_le {P k : Matrix n n ℂ} (hP : Pᴴ = P) (hk : kᴴ * k = 1) :
    ‖P - k * P * kᴴ‖ ≤ ‖⁅P, k⁆‖ := by
  have hk' : k * kᴴ = 1 := mul_eq_one_symm hk
  have hkPk : k * ⁅P, k⁆ᴴ = P - k * P * kᴴ := by simp [mul_sub, ← mul_assoc, hk', hP]
  exact (hkPk ▸ frobenius_norm_mul_of_unitary hk _).trans_le (norm_star _).le

/-- Let `k` be block diagonal for `ε` with `kᴴ k = 1`, and `P = coordProj p`. The commutator of
`k P kᴴ` with `P` is block diagonal, so it has trace zero against the part `Y - blockDiagPart ε Y`
of a matrix `Y` off the blocks. -/
lemma trace_lie_mul_sub_blockDiagPart_eq_zero {k : Matrix n n ℂ} (hk : kᴴ * k = 1)
    (hk_mem : k ∈ blockDiagAlg ε) (p : n → Prop) [DecidablePred p] (Y : Matrix n n ℂ) :
    (⁅k * coordProj p * kᴴ, coordProj p⁆ * (Y - blockDiagPart ε Y)).trace = 0 := by
  set P : Matrix n n ℂ := coordProj p
  let s : Matrix n n ℂ := signMatrix ε
  have hsP : Commute s P := commute_diagonal ..
  simp [s, blockDiagPart_eq, hsP.eq, trace_mul_comm P,
    (mem_blockDiagAlg_iff_commute.1 hk_mem).left_comm,
    inv_eq_left_inv hk ▸ blockDiagAlg.inv_mem hk_mem _ rfl, trace_mul_comm k,
    trace_mul_comm kᴴ, trace_mul_comm s, signMatrix_mul_self, mul_sub, sub_mul]
  ring_nf

/-- Let `‖u‖, ‖r‖ ≤ ‖g - 1‖ ≤ 1 / 2`, and let the commutators `B = [P, u]` and `C = [P, r]` have
norm at most that of `A = [P, g - 1]`. Then the commutator of `P` with `(1 - u) g (1 - r) - 1` is
`A - B - C` up to a term of second order, of norm at most `8 ‖g - 1‖ ‖A‖`. -/
lemma norm_lie_one_sub_mul_mul_one_sub_sub_le {P g u r : Matrix n n ℂ} (hg : ‖g - 1‖ ≤ 2⁻¹)
    (hu : ‖u‖ ≤ ‖g - 1‖) (hr : ‖r‖ ≤ ‖g - 1‖) (hB : ‖⁅P, u⁆‖ ≤ ‖⁅P, g - 1⁆‖)
    (hC : ‖⁅P, r⁆‖ ≤ ‖⁅P, g - 1⁆‖) :
    ‖⁅P, (1 - u) * g * (1 - r) - 1⁆ - (⁅P, g - 1⁆ - ⁅P, u⁆ - ⁅P, r⁆)‖ ≤
      8 * ‖g - 1‖ * ‖⁅P, g - 1⁆‖ := by
  set X : Matrix n n ℂ := g - 1
  set A : Matrix n n ℂ := ⁅P, X⁆
  set B : Matrix n n ℂ := ⁅P, u⁆
  set C : Matrix n n ℂ := ⁅P, r⁆
  have hX_nonneg : 0 ≤ ‖X‖ := norm_nonneg X
  have hA_nonneg : 0 ≤ ‖A‖ := norm_nonneg A
  -- With `m = X - u - u X` and `G = B X + u A`, the difference is `-(G + m C - (G + B - A) r)`.
  let m : Matrix n n ℂ := X - u - u * X
  let G : Matrix n n ℂ := B * X + u * A
  have hm' : ‖m‖ ≤ 3 * ‖X‖ := by
    have : ‖m‖ ≤ ‖X‖ + ‖X‖ + ‖X‖ * ‖X‖ :=
      norm_sub_le_of_le (norm_sub_le_of_le (le_refl ‖X‖) hu) (norm_mul_le_of_le hu le_rfl)
    nlinarith [mul_le_mul_of_nonneg_right hg hX_nonneg]
  have h_eq : ⁅P, (1 - u) * g * (1 - r) - 1⁆ - (A - B - C) = -(G + m * C - (G + B - A) * r) := by
    have hgX : g = 1 + X := by simp [X]
    simp only [A, B, C, G, m, hgX, lie_def]
    noncomm_ring
  rw [h_eq, norm_neg]
  have hG : ‖G‖ ≤ ‖A‖ * ‖X‖ + ‖X‖ * ‖A‖ :=
    norm_add_le_of_le (norm_mul_le_of_le hB le_rfl) (norm_mul_le_of_le hu le_rfl)
  have := norm_sub_le_of_le (norm_add_le_of_le hG (norm_mul_le_of_le hm' hC))
    (norm_mul_le_of_le (norm_sub_le_of_le (norm_add_le_of_le hG hB) (le_refl ‖A‖)) hr)
  linarith [mul_nonneg hX_nonneg hA_nonneg,
    mul_le_mul_of_nonneg_right hg (mul_nonneg hX_nonneg hA_nonneg)]

/-- The minor of a conjugate. Let `k` be block diagonal for `ε` with `kᴴ k = 1`, `P = coordProj p`,
and let `W = Y - blockDiagPart ε Y` be the part of a matrix `Y` off the blocks. If
`‖y - 1‖ ≤ δ ≤ 1 / 2`, `‖[P, y - 1] - W‖ + 2 δ ‖[P, k]‖ ≤ δ c`, `‖W‖ ≤ c` and `‖[P, k]‖ ≤ c`, then
the principal minor of `kᴴ y k` on `p` is `exp (tr (P logOneAdd (y - 1)) - tr (W ^ 2) / 4 + t)`
with `|t| ≤ 100 δ c ^ 2`. -/
lemma exists_principalMinor_conjTranspose_mul_mul_eq_exp {k y Y W : Matrix n n ℂ} {δ c : ℝ}
    (hk : kᴴ * k = 1) (hk_mem : k ∈ blockDiagAlg ε) (p : n → Prop) [DecidablePred p]
    (hW : W = Y - blockDiagPart ε Y) (hδ : δ ≤ 2⁻¹) (hy : ‖y - 1‖ ≤ δ)
    (h_near : ‖⁅coordProj p, y - 1⁆ - W‖ + 2 * δ * ‖⁅coordProj p, k⁆‖ ≤ δ * c)
    (hWc : ‖W‖ ≤ c) (hPk : ‖⁅coordProj p, k⁆‖ ≤ c) :
    ∃ t : ℂ, principalMinor (kᴴ * y * k) p =
        cexp ((coordProj p * logOneAdd (y - 1)).trace - 4⁻¹ * (W * W).trace + t) ∧
      ‖t‖ ≤ 100 * δ * c ^ 2 := by
  set P : Matrix n n ℂ := coordProj p
  have hk' : k * kᴴ = 1 := mul_eq_one_symm hk
  have hP : IsStarProjection P := isStarProjection_coordProj p
  let Q : Matrix n n ℂ := k * P * kᴴ
  have hPQ : ‖P - Q‖ ≤ ‖⁅P, k⁆‖ := norm_sub_mul_mul_conjTranspose_le hP.isSelfAdjoint hk
  -- `[Q, y - 1]` differs from `[P, y - 1]` by at most `2 δ ‖P - Q‖`.
  have h_near_Q : ‖⁅Q, y - 1⁆ - W‖ ≤ δ * c := by
    rw [show ⁅Q, y - 1⁆ - W = (y - 1) * (P - Q) - (P - Q) * (y - 1) + (⁅P, y - 1⁆ - W) by
      simp only [lie_def]; noncomm_ring]
    have := norm_add_le_of_le (norm_sub_le_of_le (norm_mul_le_of_le hy hPQ)
      (norm_mul_le_of_le hPQ hy)) (le_refl ‖⁅P, y - 1⁆ - W‖)
    linarith
  obtain ⟨t, ht_eq, ht⟩ := exists_det_compress_eq_exp_logOneAdd (P := Q) (Y := W)
    (hP.map (Unitary.conjStarAlgAut ℂ _ ⟨k, hk, hk'⟩)) hP hδ hy
    (hW ▸ trace_lie_mul_sub_blockDiagPart_eq_zero hk hk_mem p Y) h_near_Q hWc (hPQ.trans hPk)
  exact ⟨t, (principalMinor_conjTranspose_mul_mul hk y p).trans ht_eq, ht⟩

/-- Complementary minors. Let `P = coordProj p`, `X = g - 1` with `4 ‖X‖ ≤ 1 / 2` and `A = [P, X]`,
and let `y` with `‖y - 1‖ ≤ 4 ‖X‖` have the same principal minor as `g` on the complement of `p`.
If `[1 - P, y - 1]` is within `16 ‖X‖ ‖A‖` of a matrix `W` with `‖W‖ ≤ 4 ‖A‖`, then expanding both
minors gives `exp (tr ((1 - P) logOneAdd X) - tr (A ^ 2) / 4 + x)` equal to
`exp (tr ((1 - P) logOneAdd (y - 1)) - tr (W ^ 2) / 4 + z)`, with `|x| ≤ 100 ‖X‖ ‖A‖ ^ 2` and
`|z| ≤ 100 (4 ‖X‖) (4 ‖A‖) ^ 2`. -/
lemma exists_cexp_trace_one_sub_coordProj_eq {g y W : Matrix n n ℂ} (p : n → Prop)
    [DecidablePred p] (hg : 4 * ‖g - 1‖ ≤ 2⁻¹) (hy : ‖y - 1‖ ≤ 4 * ‖g - 1‖)
    (h_minor : principalMinor y (¬p ·) = principalMinor g (¬p ·))
    (h_near : ‖⁅1 - coordProj p, y - 1⁆ - W‖ ≤ 4 * ‖g - 1‖ * (4 * ‖⁅coordProj p, g - 1⁆‖))
    (hW : ‖W‖ ≤ 4 * ‖⁅coordProj p, g - 1⁆‖) :
    ∃ x z : ℂ,
      cexp (((1 - coordProj p) * logOneAdd (g - 1)).trace -
          4⁻¹ * (-⁅coordProj p, g - 1⁆ * -⁅coordProj p, g - 1⁆).trace + x) =
        cexp (((1 - coordProj p) * logOneAdd (y - 1)).trace - 4⁻¹ * (W * W).trace + z) ∧
      ‖x‖ ≤ 100 * ‖g - 1‖ * ‖⁅coordProj p, g - 1⁆‖ ^ 2 ∧
      ‖z‖ ≤ 100 * (4 * ‖g - 1‖) * (4 * ‖⁅coordProj p, g - 1⁆‖) ^ 2 := by
  set X : Matrix n n ℂ := g - 1
  set P : Matrix n n ℂ := coordProj p
  set A : Matrix n n ℂ := ⁅P, X⁆
  have hP_compl : IsStarProjection (1 - P) := (isStarProjection_coordProj p).one_sub
  have hX_half : ‖X‖ ≤ 2⁻¹ := by linarith [norm_nonneg X]
  obtain ⟨x, hx_eq, hx⟩ := exists_det_compress_eq_exp_logOneAdd (Y := -A) hP_compl hP_compl hX_half
    (le_refl ‖X‖) (by simp) (by simp [A, mul_sub, sub_mul, mul_nonneg]) (norm_neg A).le (by simp)
  obtain ⟨z, hz_eq, hz⟩ := exists_det_compress_eq_exp_logOneAdd (Y := W) hP_compl hP_compl hg hy
    (by simp) h_near hW (by simp)
  refine ⟨x, z, ?_, hx, hz⟩
  rw [← hx_eq, ← hz_eq, det_one_add_one_sub_coordProj_mul_sub_one,
    det_one_add_one_sub_coordProj_mul_sub_one, h_minor]

/-- One minor. Let `l` have gap `h`, let `X = g - 1` have norm less than `1 / 1000`, and let
`y = (1 - u) g (1 - r)`, where `u` and `r` are the parts of `X` strictly below the diagonal for the
orders `-l` and `l`, inside the blocks of `ε` (`lowerMask`). For `k ∈ K = maxCompactU ε` and the
diagonal projection `P = coordProj p` to a set `p` of lowest entries of `l`, the principal minor of
`kᴴ y k` on `p` is `exp (tr (P logOneAdd X) + ‖[P, X]‖² / 4 + r')` with
`|r'| ≤ 2 · 10⁵ ‖X‖ (‖[P, X]‖² + ‖[P, k]‖²)`. -/
private lemma exists_principalMinor_one_sub_mul_mul_one_sub_eq_exp (hl : l.HasGap h)
    {g : USign ε} (hg : ‖(g : Matrix n n ℂ) - 1‖ < 1000⁻¹) (p : n → Prop) [DecidablePred p]
    (hp : ∀ i j, p i → ¬p j → l i < l j) (κ : maxCompactU ε) :
    ∃ r : ℂ,
      principalMinor ((κ : Matrix n n ℂ)ᴴ *
          ((1 - lowerMask ε (-l) ((g : Matrix n n ℂ) - 1)) * (g : Matrix n n ℂ) *
            (1 - lowerMask ε l ((g : Matrix n n ℂ) - 1))) * (κ : Matrix n n ℂ)) p =
        cexp ((coordProj p * logOneAdd ((g : Matrix n n ℂ) - 1)).trace +
          ‖⁅coordProj p, (g : Matrix n n ℂ) - 1⁆‖ ^ 2 / 4 + r) ∧
      ‖r‖ ≤ 200000 * ‖(g : Matrix n n ℂ) - 1‖ *
        (‖⁅coordProj p, (g : Matrix n n ℂ) - 1⁆‖ ^ 2 +
          ‖⁅coordProj p, (κ : Matrix n n ℂ)⁆‖ ^ 2) := by
  set X : Matrix n n ℂ := (g : Matrix n n ℂ) - 1
  have hX_nonneg : 0 ≤ ‖X‖ := norm_nonneg X
  have hX_half : ‖X‖ ≤ 2⁻¹ := by linarith
  have hX_four : 4 * ‖X‖ ≤ 2⁻¹ := by linarith
  -- `u` and `r` are the parts of `X` strictly below the diagonal for the orders `-l` and `l`,
  -- inside the blocks of `ε`.
  let u : Matrix n n ℂ := lowerMask ε (-l) X
  let r : Matrix n n ℂ := lowerMask ε l X
  let y : Matrix n n ℂ := (1 - u) * g * (1 - r)
  have hu : ‖u‖ ≤ ‖X‖ := norm_entryMask_le
  have hr : ‖r‖ ≤ ‖X‖ := norm_entryMask_le
  have hy_near : ‖y - 1‖ ≤ 4 * ‖X‖ := norm_one_sub_mul_mul_one_sub_sub_one_le hg hu hr
  -- On a set of highest entries of `l` the triangular factors do not change the minor.
  have h_minor (q : n → Prop) [DecidablePred q] (hq : ∀ i j, q i → ¬q j → l j < l i) :
      principalMinor y q = principalMinor (g : Matrix n n ℂ) q :=
    principalMinor_one_sub_mul_mul_one_sub hl (fun i j h ↦ by simp [u]; grind)
      (fun i j h ↦ by simp [r]; grind) hq
  -- Notation: `P` projects to `p`, and `A`, `B`, `C` are the commutators of `P` with `X`, `u`, `r`.
  set k : Matrix n n ℂ := (κ : Matrix n n ℂ)
  let s : Matrix n n ℂ := signMatrix ε
  have hk : kᴴ * k = 1 := (U_one_mem_unitaryGroup ⟨_, κ.property⟩).1
  have hk_mem : k ∈ blockDiagAlg ε := mem_maxCompactU.1 κ.property
  have hsP : Commute s (coordProj p) := commute_diagonal ..
  set P : Matrix n n ℂ := coordProj p
  set A : Matrix n n ℂ := ⁅P, X⁆
  set B : Matrix n n ℂ := ⁅P, u⁆
  set C : Matrix n n ℂ := ⁅P, r⁆
  let V : Matrix n n ℂ := (1 + X)⁻¹ - 1
  have h_mask (c : n → ℤ) : ⁅P, lowerMask ε c X⁆ = lowerMask ε c A :=
    lie_coordProj_entryMask p _ X
  have hB : B = blockDiagPart ε A - C := by
    rw [eq_sub_iff_add_eq, blockDiagPart_lie_coordProj hp X]
    exact congrArg₂ (· + ·) (h_mask (-l)) (h_mask l)
  have hA_nonneg : 0 ≤ ‖A‖ := norm_nonneg A
  have hPk_nonneg : 0 ≤ ‖⁅P, k⁆‖ := norm_nonneg _
  have hP_star : Pᴴ = P := (isStarProjection_coordProj p).isSelfAdjoint
  have hV : ‖V‖ ≤ 2 * ‖X‖ := norm_inv_one_add_sub_one_le hX_half
  have hB_le : ‖B‖ ≤ ‖A‖ := norm_lie_coordProj_entryMask_le p _ X
  have hC_le : ‖C‖ ≤ ‖A‖ := norm_lie_coordProj_entryMask_le p _ X
  have hg_star : (g : Matrix n n ℂ)ᴴ = s * (g : Matrix n n ℂ)⁻¹ * s := by
    grind [signMatrix_mul_self, U.inv_coe_eq_mul_conjTranspose_mul g]
  -- `[P, y - 1]` is `A - B - C` up to a term of second order.
  have h_lie : ‖⁅P, y - 1⁆ - (A - B - C)‖ ≤ 8 * ‖X‖ * ‖A‖ :=
    norm_lie_one_sub_mul_mul_one_sub_sub_le hX_half hu hr hB_le hC_le
  -- The complementary minors of `g` and of `y`, which agree.
  obtain ⟨x, z, hz_eq, hx, hz⟩ : ∃ x z : ℂ,
      cexp (((1 - P) * logOneAdd X).trace - 4⁻¹ * (-A * -A).trace + x) =
        cexp (((1 - P) * logOneAdd (y - 1)).trace -
          4⁻¹ * ((B + C - A) * (B + C - A)).trace + z) ∧
      ‖x‖ ≤ 100 * ‖X‖ * ‖A‖ ^ 2 ∧ ‖z‖ ≤ 100 * (4 * ‖X‖) * (4 * ‖A‖) ^ 2 :=
    exists_cexp_trace_one_sub_coordProj_eq p hX_four hy_near (h_minor _ (by tauto)) (by
      rw [show ⁅1 - P, y - 1⁆ - (B + C - A) = -(⁅P, y - 1⁆ - (A - B - C)) by
        simp only [lie_def]; noncomm_ring, norm_neg]
      linarith [mul_nonneg hX_nonneg hA_nonneg])
    (by linarith [norm_sub_le_of_le (norm_add_le_of_le hB_le hC_le) (le_refl ‖A‖)])
  -- The minor of `kᴴ y k` on `p`.
  obtain ⟨t, ht_eq, ht⟩ : ∃ t : ℂ, principalMinor (kᴴ * y * k) p =
        cexp ((P * logOneAdd (y - 1)).trace - 4⁻¹ * ((A - B - C) * (A - B - C)).trace + t) ∧
      ‖t‖ ≤ 100 * (4 * ‖X‖) * (4 * (‖A‖ + ‖⁅P, k⁆‖)) ^ 2 :=
    exists_principalMinor_conjTranspose_mul_mul_eq_exp hk hk_mem p (Y := A) (by rw [hB]; abel)
      hX_four hy_near
      (by linarith [mul_nonneg hX_nonneg hA_nonneg, mul_nonneg hX_nonneg hPk_nonneg])
      (by linarith [norm_sub_le_of_le (norm_sub_le_of_le (le_refl ‖A‖) hB_le) hC_le])
      (by linarith)
  have h_det : cexp (logOneAdd (y - 1)).trace = cexp (logOneAdd X).trace := by
    rw [← det_one_add_eq_exp_trace_logOneAdd (hy_near.trans hX_four),
      ← det_one_add_eq_exp_trace_logOneAdd hX_half]
    simpa [principalMinor_of_forall, X] using h_minor ⊤
  -- The remainder: those of the three determinants, and the difference between `‖A‖ ^ 2` and
  -- `-tr (A ^ 2)`, which comes from `Xᴴ = s ((1 + X)⁻¹ - 1) s`.
  have h_corr : ‖((4⁻¹ : ℝ) • (V * (A * V + A) + A * V) * (A - B - C - B - C)).trace‖ ≤
      (2 * ‖X‖ * (‖A‖ * (2 * ‖X‖) + ‖A‖) + ‖A‖ * (2 * ‖X‖)) *
        (‖A‖ + ‖A‖ + ‖A‖ + ‖A‖ + ‖A‖) :=
    norm_trace_mul_le (norm_smul_le_of_le_one 4⁻¹ (norm_add_le_of_le (norm_mul_le_of_le hV
      (norm_add_le_of_le (norm_mul_le_of_le le_rfl hV) le_rfl)) (norm_mul_le_of_le le_rfl hV))
      ⟨by norm_num, by norm_num⟩) (norm_sub_le_of_le (norm_sub_le_of_le (norm_sub_le_of_le
      (norm_sub_le_of_le le_rfl hB_le) hC_le) hB_le) hC_le)
  refine ⟨t + z - x + ((4⁻¹ : ℝ) • (V * (A * V + A) + A * V) * (A - B - C - B - C)).trace, ?_, ?_⟩
  · -- Multiply by the complementary minor and by `det y = det g`, and compare exponents.
    refine ht_eq.trans (mul_right_cancel₀ (by simp) (congr(_ * ($hz_eq * $h_det)).trans ?_))
    simp [V, s, hg_star, hP_star, hB, blockDiagPart_eq, hsP.eq, trace_mul_comm P,
      ← ofReal_pow, A, X, trace_mul_comm s, signMatrix_mul_self, ← mul_assoc s s, ← exp_add,
      mul_sub, sub_mul, ← trace_star_mul_self_eq_norm_sq]
    ring_nf
  · have := norm_add_le_of_le (norm_sub_le_of_le (norm_add_le_of_le ht hz) hx) h_corr
    linarith [mul_nonneg hX_nonneg (sq_nonneg ‖A‖), mul_nonneg hX_nonneg (sq_nonneg ‖⁅P, k⁆‖),
      mul_nonneg hX_nonneg (sq_nonneg (‖A‖ - ‖⁅P, k⁆‖)),
      mul_le_mul_of_nonneg_right hX_half (mul_nonneg hX_nonneg (sq_nonneg ‖A‖))]

/-- Let `l` have gap `h` and let `X = g - 1` have norm less than `1 / 1000`. There is a matrix `y`
with `l.dsCoeff g = l.flenstedJensen 1 y` such that, for `k ∈ K = maxCompactU ε` and the diagonal
projection `P = coordProj p` to a set `p` of lowest entries of `l`, the principal minor of
`kᴴ y k` on `p` is `exp (tr (P logOneAdd X) + ‖[P, X]‖² / 4 + r)` with
`|r| ≤ 2 · 10⁵ ‖X‖ (‖[P, X]‖² + ‖[P, k]‖²)`. -/
lemma exists_principalMinor_eq_exp (hl : l.HasGap h) (g : USign ε)
    (hg : ‖(g : Matrix n n ℂ) - 1‖ < 1000⁻¹) :
    ∃ y : Matrix n n ℂ, l.dsCoeff g = l.flenstedJensen 1 y ∧
      ∀ (p : n → Prop) [DecidablePred p], (∀ i j, p i → ¬p j → l i < l j) →
        ∀ k : maxCompactU ε, ∃ r : ℂ,
          principalMinor ((k : Matrix n n ℂ)ᴴ * y * (k : Matrix n n ℂ)) p =
            cexp ((coordProj p * logOneAdd ((g : Matrix n n ℂ) - 1)).trace +
              ‖⁅coordProj p, (g : Matrix n n ℂ) - 1⁆‖ ^ 2 / 4 + r) ∧
          ‖r‖ ≤ 200000 * ‖(g : Matrix n n ℂ) - 1‖ *
            (‖⁅coordProj p, (g : Matrix n n ℂ) - 1⁆‖ ^ 2 +
              ‖⁅coordProj p, (k : Matrix n n ℂ)⁆‖ ^ 2) := by
  set X : Matrix n n ℂ := (g : Matrix n n ℂ) - 1
  -- `r c` is the part of `X` strictly below the diagonal for the order `c`, inside the blocks of
  -- `ε`. Multiply `g` by the unipotent factors `1 - u` and `1 - r c`.
  let r (c : n → ℤ) : Matrix n n ℂ := lowerMask ε c X
  let u : Matrix n n ℂ := r (-l)
  let y (c : n → ℤ) : Matrix n n ℂ := (1 - u) * g * (1 - r c)
  have hy_near (c : n → ℤ) : ‖y c - 1‖ ≤ 4 * ‖X‖ :=
    norm_one_sub_mul_mul_one_sub_sub_one_le hg norm_entryMask_le norm_entryMask_le
  -- Step 1: the coefficient is `l.flenstedJensen 1 (y l)`. Removing either factor conjugates the
  -- value.
  have hy_acc (c : n → ℤ) : (y c).IsAccretive :=
    isAccretive_of_norm_sub_one_lt ((hy_near c).trans_lt (by linarith))
  have hg_acc : (g : Matrix n n ℂ).IsAccretive :=
    isAccretive_of_norm_sub_one_lt (hg.trans (by norm_num))
  have hug_acc : ((1 - u) * (g : Matrix n n ℂ)).IsAccretive := by
    simpa [y, show r 0 = 0 from rfl] using hy_acc 0
  have h_coeff : l.dsCoeff g = l.flenstedJensen 1 (y l) :=
    dsCoeff_eq_flenstedJensen_one_sub_mul_mul_one_sub hl (fun i j h ↦ by simp [u, r]; grind)
      (fun i j h ↦ by simp [r]; grind) hg_acc hug_acc (hy_acc l)
  -- Steps 2 and 3: the minors of the conjugates of `y l` under `K`.
  exact ⟨y l, h_coeff, fun p _ hp κ ↦
    exists_principalMinor_one_sub_mul_mul_one_sub_eq_exp hl hg p hp κ⟩

end New.DiscreteSeries

end MinorExpansion
