module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFrameMemFlagDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImEmbHermSelf

@[expose] public section

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_frame_mem_flagDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ u : Fin r → Fin r → E, GlobalTheory.OrthoFrame.frm X.Ψ u ∈ X.dom := by
  exact @GlobalTheory.OrthoFrame.exists_frm_mem_dom
