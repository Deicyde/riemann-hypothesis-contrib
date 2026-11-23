module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerCharacterFrameFirstStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsFiniteDimensionalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxSlopeSqLeOfNoShortVectorStatement

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.LamMuMax

/-- Parametric `slopeMax_sq` upper bound given any Petersson mean-log lower bound and finrank bound
for constant `K`. -/
theorem slopeMax_le_of_bounds (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E)
    (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (L K : ℝ)
    (hG : GoodW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n)) (h0 : latW U (wtZ a n) ≠ ⊥)
    (hP : ∀ F : cuspW Xo c U (wtZ a n), F ∈ latW U (wtZ a n) → F ≠ 0 →
      -(L + 1 / 2 * Real.log K) ≤
        (∑ σ : c.F →+* ℂ, Real.log (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) σ F)) /
          (Module.finrank ℚ c.F : ℝ))
    (hR : FiniteDimensional c.F (cuspW Xo c U (wtZ a n)) ∧
      (Module.finrank c.F (cuspW Xo c U (wtZ a n)) : ℝ) ≤ K) :
    slopeMax_sq (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n)) (latW U (wtZ a n)) ≤
      2 * L + 2 * Real.log K + Real.log |(discr c.F : ℝ)| / (Module.finrank ℚ c.F : ℝ) := by
  have hTC : IsTotallyComplex c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  have hj : ∀ (σ : c.F →+* ℂ) (f : cuspW Xo c U (wtZ a n)),
      normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) ((starRingEnd ℂ).comp σ) f =
        normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) σ f := fun σ f => by
    rw [normW, normW, petW, petW, GlobalTheory.CompHt.goodOf_conj σ]
  have hS := GlobalTheory.T.maxSlope_sq_le_of_no_short_vector c.F (cuspW Xo c U (wtZ a n)) (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n))
    (latW U (wtZ a n)) _ hG.1 hj hG.2.1 h0 hP
  have := hR.1
  obtain ⟨F, hF, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have : Nontrivial (cuspW Xo c U (wtZ a n)) := ⟨⟨F, 0, hF0⟩⟩
  have hpos : (0 : ℝ) < (Module.finrank c.F (cuspW Xo c U (wtZ a n)) : ℝ) := by
    exact_mod_cast Module.finrank_pos
  have hlog := Real.log_le_log hpos hR.2
  linarith

theorem slopeMax_le : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → GoodW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) → latW U (wtZ a n) ≠ ⊥ → slopeMax_sq (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n)) (latW U (wtZ a n)) ≤ 2 * lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 2 * Real.log (supConst D.host.E D.R.r D.host.d l.M (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1)) + Real.log |(discr c.F : ℝ)| / (Module.finrank ℚ c.F : ℝ) :=
  fun hMass hTor D j H Dw l Xo c U dict hL _ χ hχ a n hD hG h0 =>
    slopeMax_le_of_bounds D j H Dw l Xo c U dict a n _ _ hG h0
      (fun F hF hF0 => (GlobalTheory.T.kronecker_character_frame_first hMass hTor D j H Dw l Xo c U dict hL χ hχ a n hD F hF hF0).2)
      (GlobalTheory.LevGeo.RankBd.finrank_cuspW_le hMass hTor D j H Dw l Xo c U dict hL a n hD)

end GlobalTheory.LamMuMax
