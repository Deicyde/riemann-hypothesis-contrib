module

public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.NormCpowSubLePoint

@[expose] public section

open Complex Filter Topology

noncomputable section

namespace Formalism.ZF

namespace ComplexPowerDifferenceIntegral

def dz (s : ℂ) (n : ℕ) : ℂ :=
  (((n : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s) - ((((n : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (1 - s) -
    (s - 1) * ((((n : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (-s)

def Dz (s : ℂ) : ℂ := ∑' n, dz s n

lemma norm_dz_le {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖dz s n‖ ≤ ‖s - 1‖ * ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := by
  have ha : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [dz, d_eq ha s, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_eint_le ha hs) (norm_nonneg _)

lemma summable_norm_dz {s : ℂ} (hs : 0 < s.re) : Summable (fun n => ‖dz s n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_dz_le hs)
    ((summable_shift (by linarith : -s.re - 1 < -1)).mul_left _)

lemma Dz_differentiableOn : DifferentiableOn ℂ Dz {s : ℂ | 0 < s.re} := by
  intro s0 hs0
  let U : Set ℂ := {s | s0.re / 2 < s.re} ∩ Metric.ball s0 1
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hmem : s0 ∈ U := ⟨by show s0.re / 2 < s0.re; linarith [show 0 < s0.re from hs0], Metric.mem_ball_self one_pos⟩
  have hdiff : ∀ n : ℕ, DifferentiableOn ℂ (fun s => dz s n) U := fun n =>
    (Differentiable.differentiableOn fun s => by
      have h1 : (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : ((n : ℝ) + 1) ≠ 0)
      have h2 : ((((n : ℝ) + 1) + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : ((n : ℝ) + 1 + 1) ≠ 0)
      exact (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl h1) |>.sub
        (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl h2))).sub
        ((differentiableAt_id.sub_const 1).mul (differentiableAt_id.neg.const_cpow (Or.inl h2))))
  have hbound : ∀ n : ℕ, ∀ s ∈ U,
      ‖dz s n‖ ≤ (‖s0‖ + 1 + 1) * (‖s0‖ + 1) * ((n : ℝ) + 1) ^ (-(s0.re / 2) - 1) := fun n s hs => by
    have hd : ‖s - s0‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hs.2
    have hre : s0.re / 2 < s.re := hs.1
    have hpos : 0 < s.re := by linarith [show 0 < s0.re from hs0]
    have hsR : ‖s‖ ≤ ‖s0‖ + 1 := by linarith [norm_sub_norm_le s s0]
    have hs1 : ‖s - 1‖ ≤ ‖s0‖ + 1 + 1 := by linarith [norm_sub_le s 1, norm_one (α := ℂ)]
    have hp : ((n : ℝ) + 1) ^ (-s.re - 1) ≤ ((n : ℝ) + 1) ^ (-(s0.re / 2) - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith)
    exact (norm_dz_le hpos n).trans (by gcongr)
  have hD := differentiableOn_tsum_of_summable_norm ((summable_shift (by linarith [show 0 < s0.re from hs0])).mul_left _)
    hdiff hU hbound
  exact (hD.differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt

end ComplexPowerDifferenceIntegral

end Formalism.ZF
