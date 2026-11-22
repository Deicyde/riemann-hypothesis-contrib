module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.Liouville

@[expose] public section

open Complex Metric

noncomputable section

namespace Formalism.ZF

lemma zflb_exists_log {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (ball z₀ R)) (hne : ∀ z ∈ ball z₀ R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, g z₀ = 0 ∧ (∀ z ∈ ball z₀ R, HasDerivAt g (deriv f z / f z) z) ∧
      ∀ z ∈ ball z₀ R, f z = f z₀ * Complex.exp (g z) := by
  obtain ⟨G, hG⟩ := ((hf.deriv isOpen_ball).div hf hne).isExactOn_ball
  refine ⟨fun z => G z - G z₀, by simp, fun z hz => (hG z hz).sub_const _, ?_⟩
  have hk : ∀ z ∈ ball z₀ R, HasDerivAt (fun w => f w * Complex.exp (-(G w - G z₀))) 0 z := fun z hz => by
    have hfz := (hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have hgz : HasDerivAt (fun w => -(G w - G z₀)) (-(deriv f z / f z)) z := ((hG z hz).sub_const (G z₀)).neg
    have h := hfz.mul hgz.cexp
    have h1 := hne z hz
    exact (show deriv f z * Complex.exp (-(G z - G z₀)) +
      f z * (Complex.exp (-(G z - G z₀)) * -(deriv f z / f z)) = 0 by field_simp; ring) ▸ h
  intro z hz
  have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z₀ R).isPreconnected
    (fun w hw => (hk w hw).differentiableAt.differentiableWithinAt) (fun w hw => (hk w hw).deriv)
    hz (mem_ball_self (pos_of_mem_ball hz))
  simp only [sub_self, neg_zero, Complex.exp_zero, mul_one] at hconst
  rw [← hconst, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

theorem logDerivBoundOnBall : LogDerivBound := by
  intro f z₀ R M hR hM hf hne hbd z hz
  obtain ⟨g, hg0, hgd, hgf⟩ := zflb_exists_log (hf.mono ball_subset_closedBall)
    fun w hw => hne w (ball_subset_closedBall hw)
  have hf0 : 0 < ‖f z₀‖ := norm_pos_iff.2 (hne z₀ (mem_closedBall_self hR.le))
  have hre : ∀ w ∈ ball z₀ R, (g w).re ≤ Real.log M := fun w hw => by
    have h1 := hbd w (ball_subset_closedBall hw)
    rw [hgf w hw, norm_mul, Complex.norm_exp] at h1
    have h2 : Real.exp (g w).re ≤ M := le_of_not_gt fun h => by linarith [mul_lt_mul_of_pos_left h hf0]
    exact (Real.log_exp _).symm.trans_le (Real.log_le_log (Real.exp_pos _) h2)
  have hshift : ∀ v ∈ ball (0 : ℂ) R, z₀ + v ∈ ball z₀ R := fun v hv => by
    simpa [mem_ball, dist_eq_norm] using hv
  have hmain : ∀ A : ℝ, Real.log M < A → ‖deriv f z / f z‖ ≤ 24 * A / R := fun A hA => by
    have hA0 : 0 < A := (Real.log_nonneg hM).trans_lt hA
    have hhd : DifferentiableOn ℂ (fun v => g (z₀ + v)) (ball 0 R) := fun v hv =>
      ((hgd _ (hshift v hv)).differentiableAt.comp v (differentiableAt_id.const_add z₀)).differentiableWithinAt
    have hhm : Set.MapsTo (fun v => g (z₀ + v)) (ball 0 R) {w | w.re ≤ A} :=
      fun v hv => (hre _ (hshift v hv)).trans hA.le
    have hbc : ∀ w ∈ closedBall z₀ (3 * R / 4), ‖g w‖ ≤ 6 * A := fun w hw => by
      obtain ⟨u, rfl⟩ : ∃ u, w = z₀ + u := ⟨w - z₀, by ring⟩
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left] at hw
      have hB := Complex.borelCaratheodory_zero hA0 hhd hhm hR
        (mem_ball_zero_iff.2 (by linarith)) (by simpa using hg0)
      exact hB.trans ((div_le_iff₀ (by linarith)).2 (by nlinarith [norm_nonneg u]))
    have hR4 : 0 < R / 4 := by linarith
    have hsub : closedBall z (R / 4) ⊆ ball z₀ R := fun w hw =>
      lt_of_le_of_lt (dist_triangle w z z₀) (by linarith [mem_closedBall.1 hw, mem_closedBall.1 hz])
    have hdiff : DiffContOnCl ℂ g (ball z (R / 4)) := DifferentiableOn.diffContOnCl <| by
      rw [closure_ball z hR4.ne']; exact fun w hw => (hgd w (hsub hw)).differentiableAt.differentiableWithinAt
    have hC : ∀ w ∈ sphere z (R / 4), ‖g w‖ ≤ 6 * A := fun w hw =>
      hbc w <| (dist_triangle w z z₀).trans (by linarith [mem_sphere.1 hw, mem_closedBall.1 hz])
    have hder := norm_deriv_le_of_forall_mem_sphere_norm_le hR4 hdiff hC
    rw [(hgd z (hsub (mem_closedBall_self hR4.le))).deriv] at hder
    exact hder.trans_eq (by field_simp; ring)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h := hmain (Real.log M + ε * R / 24) (by linarith [show 0 < ε * R / 24 by positivity])
  exact h.trans_eq (by field_simp)

end Formalism.ZF
