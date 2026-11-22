module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv

@[expose] public section

open Complex Set Filter Topology

noncomputable section

namespace Formalism.ZF

def laHfun (y : ℝ) (s : ℂ) : ℂ :=
  (1 - (s - 1) * (deriv riemannZeta₁ s / riemannZeta₁ s)) * ((y : ℂ) ^ s / s)

def laU : Set ℂ := {s | riemannZeta₁ s ≠ 0} ∩ {s | s ≠ 0}

theorem laU_open : IsOpen laU :=
  (isOpen_ne_fun differentiable_riemannZeta₁.continuous continuous_const).inter isOpen_ne

theorem one_mem_laU : (1 : ℂ) ∈ laU := by simp [laU]

theorem laH_diffOn (y : ℝ) (hy : 0 < y) : DifferentiableOn ℂ (laHfun y) laU := fun s hs => by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  exact (((differentiableAt_const _).sub ((differentiableAt_id.sub_const 1).mul
    ((differentiable_riemannZeta₁.deriv s).div (differentiable_riemannZeta₁ s) hs.1))).mul
    ((differentiableAt_id.const_cpow (Or.inl hy0)).div differentiableAt_id hs.2)).differentiableWithinAt

theorem laH_one (y : ℝ) : laHfun y 1 = y := by simp [laHfun]

theorem laH_deriv_one (y : ℝ) (hy : 0 < y) :
    deriv (laHfun y) 1 = (y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hB : DifferentiableAt ℂ (fun s => deriv riemannZeta₁ s / riemannZeta₁ s) 1 :=
    (differentiable_riemannZeta₁.deriv 1).div (differentiable_riemannZeta₁ 1) (by simp)
  have hk := (((hasDerivAt_id' (1 : ℂ)).sub_const 1).mul hB.hasDerivAt).const_sub 1
  have hc : HasDerivAt (fun s : ℂ => (y : ℂ) ^ s) ((y : ℂ) ^ (1 : ℂ) * Complex.log y) 1 := by
    simpa using (hasStrictDerivAt_const_cpow (x := (y : ℂ)) (y := 1) (Or.inl hy0)).hasDerivAt
  have hh : HasDerivAt (laHfun y) _ 1 := hk.mul (hc.div (hasDerivAt_id' (1 : ℂ)) one_ne_zero)
  rw [hh.deriv, ← Complex.ofReal_log hy.le]
  simp; ring

theorem laurentExpansionAtOne : LaurentAtOne := by
  intro y hy
  set h := laHfun y
  have hn : laU ∈ 𝓝 (1 : ℂ) := laU_open.mem_nhds one_mem_laU
  refine ⟨dslope (dslope h 1) 1,
    ((differentiableOn_dslope hn).2 ((differentiableOn_dslope hn).2 (laH_diffOn y hy))).differentiableAt hn, ?_⟩
  filter_upwards [log_deriv_riemannZeta_eq_neg_inv_sub_add, nhdsWithin_le_nhds hn, self_mem_nhdsWithin]
    with w hw hwU hw1
  have hw1' : w - 1 ≠ 0 := sub_ne_zero.2 hw1
  have hw0 : w ≠ 0 := hwU.2
  have e1 : (w - 1) * dslope h 1 w = h w - y := by simpa [h, laH_one] using sub_smul_dslope h 1 w
  have e2 : (w - 1) * dslope (dslope h 1) 1 w = dslope h 1 w -
      ((y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y) := by
    simpa [dslope_same, h, laH_deriv_one y hy] using sub_smul_dslope (dslope h 1) 1 w
  have hhw : h w = (1 - (w - 1) * (deriv riemannZeta₁ w / riemannZeta₁ w)) * ((y : ℂ) ^ w / w) := rfl
  unfold Fy; rw [hw]
  generalize deriv riemannZeta₁ w / riemannZeta₁ w = B at hhw ⊢
  generalize (y : ℂ) ^ w = P at hhw ⊢
  generalize dslope (dslope h 1) 1 w = q at e2 ⊢
  generalize dslope h 1 w = D at e1 e2
  generalize h w = H at e1 hhw
  have key : (1 - (w - 1) * B) * (P / w) =
      y + (w - 1) * (((y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y) + (w - 1) * q) := by
    rw [← hhw]; linear_combination -e1 - (w - 1) * e2
  rw [show -(-(w - 1)⁻¹ + B) * P / (w * (w - 1)) = (1 - (w - 1) * B) * (P / w) / (w - 1) ^ 2 by field_simp; ring, key]
  field_simp; ring

end Formalism.ZF
