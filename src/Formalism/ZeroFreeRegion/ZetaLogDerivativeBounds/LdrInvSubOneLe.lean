module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZfoGrowthBall

@[expose] public section

open Complex Metric

noncomputable section

namespace Formalism.ZF

lemma ldr_inv_sub_one_le {s : ℂ} (h : 1 ≤ |s.im|) : ‖1 / (s - 1)‖ ≤ 1 := by
  have h1 : |s.im| ≤ ‖s - 1‖ := by simpa using Complex.abs_im_le_norm (s - 1)
  rw [norm_div, norm_one, div_le_one (by linarith)]; linarith

end Formalism.ZF
