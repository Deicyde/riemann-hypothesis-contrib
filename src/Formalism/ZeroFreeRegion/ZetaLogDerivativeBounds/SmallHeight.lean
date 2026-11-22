module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv

@[expose] public section

open Complex Set Filter Topology

noncomputable section

namespace Formalism.ZF

theorem zeroFreeBoundedHeight : SmallHeight := by
  intro T
  have hopen : IsOpen {s : ℂ | s ≠ 1 → riemannZeta s ≠ 0} := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    by_cases hz1 : z = 1
    · subst hz1
      filter_upwards [eventually_nhdsWithin_iff.mp (riemannZeta_residue_one.eventually_ne one_ne_zero)]
        with x hx hx1 using right_ne_zero_of_mul (hx hx1)
    · filter_upwards [(differentiableAt_riemannZeta hz1).continuousAt.eventually_ne (hz hz1)]
        with x hx _ using hx
  set K : Set ℂ := (fun y : ℝ => (1 : ℂ) + (y : ℂ) * I) '' Icc (-T) T
  have hKc : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hKsub : K ⊆ {s : ℂ | s ≠ 1 → riemannZeta s ≠ 0} := by
    rintro _ ⟨y, -, rfl⟩ _; exact riemannZeta_ne_zero_of_one_le_re (by simp)
  obtain ⟨δ, hδ, hsub⟩ := hKc.exists_cthickening_subset_open hopen hKsub
  refine ⟨δ, hδ, fun s hs hre hs1 => ?_⟩
  by_cases hle : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hle
  · have hd : dist s ((1 : ℂ) + (s.im : ℂ) * I) ≤ δ := by
      rw [Complex.dist_of_im_eq (by simp), Real.dist_eq, abs_le]; simp; constructor <;> linarith
    exact hsub (Metric.mem_cthickening_of_dist_le _ _ _ _ ⟨s.im, abs_le.mp hs, rfl⟩ hd) hs1

end Formalism.ZF
