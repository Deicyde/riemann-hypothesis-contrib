module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ConstantSupremum.SupremumConstantLogBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedFrameSumPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerCharacterFrameFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerCharacterFrameSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedFrameSumSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerCharacterFrameThird
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGeometryWeightBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupConstantLogBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneWeightLogBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeMaxSquaredBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneWeightLogBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeMaxSquaredBoundStatement

@[expose] public section

/-!
# Unconditional Tamagawa–Bergman–Petersson Pipeline (`supConst2`)

Instantiates the parametric Bergman sup-norm, Petersson comparison, cusp-form rank, and
maximal-slope bounds from `Development.AbelianVarietyTheory.Proofs.DivisorProofs.*` using the
unconditional fundamental-domain volume bound `MainStatements.Tam.massLev2` and supremum constant
`MainStatements.Tam.Plug.supConst2`, and records the sharper quadratic-in-`(f, r)`,
linear-in-`Lb` log bound `UpperTheory.Lit.Tam.supConst2_log_le_quadratic`.
-/

noncomputable section

namespace UpperTheory.Lit.Tam

def lamPet2 (E : Type) [Field E] [NumberField E] (r q d M : ℕ) (Om s t : ℝ) : ℝ :=
  GlobalTheory.LevGeo.lamSup E r q d M Om s t +
    1 / 2 * Real.log (MainStatements.Tam.Plug.supConst2 E r d M (s + t + 1))

end UpperTheory.Lit.Tam

section
set_option synthInstance.maxHeartbeats 400000
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions
  Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

theorem UpperTheory.Lit.Tam.tamagawa_local_volume_factor :
    True → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ)
      (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H)
      (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l)
      (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
      (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r),
      Laws D j Xo c U dict → ∀ σ, GoodEmb c σ →
      ∀ (la : ∀ k, Wt ((U σ).X k).Ψ D.R.r) (w : ℝ), 0 < w →
      (∀ k, (∑ τ, ((U σ).X k).spread (la k) τ) ≤ w) →
      (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (la k) γ = 1) →
      ∀ P ∈ holSub (U σ).X la,
        supE (U σ).X la P ^ 2 ≤
          ENNReal.ofReal (MainStatements.Tam.Plug.supConst2 D.host.E D.R.r D.host.d l.M w) *
            petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 :=
  fun _ _ D j H Dw l Xo c U dict hLw σ hσ la w hw0 hspread hχ P hP =>
    GlobalTheory.SupModel.supPet_principal_of_mass D j H Dw l Xo c U dict hLw σ hσ la w
      (MainStatements.Tam.massLev2 D.host.E D.R.r l.M) hw0 hspread hχ
      (MainStatements.Tam.Plug.comp D j H Dw l Xo c U dict hLw σ hσ) P hP

theorem UpperTheory.Lit.Tam.finrank_cuspW_le_supConst2 :
    True → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ)
      (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H)
      (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l)
      (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
      (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r),
      Laws D j Xo c U dict → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n →
      FiniteDimensional c.F (cuspW Xo c U (wtZ a n)) ∧
        (Module.finrank c.F (cuspW Xo c U (wtZ a n)) : ℝ) ≤
          MainStatements.Tam.Plug.supConst2 D.host.E D.R.r D.host.d l.M
            (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1) :=
  fun hM hT D j H Dw l Xo c U dict hL a n hDom =>
    GlobalTheory.LevGeo.RankBd.finrank_cuspW_le_of_sup D j H Dw l Xo c U dict hL a n hDom _
      (MainStatements.Tam.Plug.supConst_nonneg2 _ _ _ _ _)
      fun σ hσ la w hw hsp hχ hw_eq => hw_eq ▸
        UpperTheory.Lit.Tam.tamagawa_local_volume_factor hM hT D j H Dw l Xo c U dict hL σ hσ la w hw hsp hχ

theorem UpperTheory.Lit.Tam.petersson_norm_tamagawa_formula :
    True → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ)
      (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H)
      (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l)
      (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
      (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r),
      Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d),
      GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n →
      ∀ F : cuspW Xo c U (wtZ a n), F ∈ latW U (wtZ a n) → F ≠ 0 →
      (∀ σ, 0 < normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) σ F) ∧
        -UpperTheory.Lit.Tam.lamPet2 D.host.E D.R.r Dw.q D.host.d l.M
            (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ)
            ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) ≤
          (∑ σ : c.F →+* ℂ, Real.log (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) σ F)) /
            (Module.finrank ℚ c.F : ℝ) :=
  fun hM hT D j H Dw l Xo c U dict hL _ χ hχ a n hD F hF hF0 =>
    GlobalTheory.LamPet.mean_log_petersson_ge_of_sup D j H Dw l Xo c U dict hL χ hχ a n hD _
      (fun σ hσ la w hw hsp hchi hw_eq => hw_eq ▸
        UpperTheory.Lit.Tam.tamagawa_local_volume_factor hM hT D j H Dw l Xo c U dict hL σ hσ la w hw hsp hchi)
      F hF hF0

theorem UpperTheory.Lit.Tam.petersson_norm_local_factor_eq :
    True → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ)
      (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H)
      (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l)
      (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
      (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r),
      Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d),
      GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n →
      GoodW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) → latW U (wtZ a n) ≠ ⊥ →
      slopeMax_sq (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n)) (latW U (wtZ a n)) ≤
        2 * lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re
            ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) +
          2 * Real.log (MainStatements.Tam.Plug.supConst2 D.host.E D.R.r D.host.d l.M
            (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1)) +
          Real.log |(discr c.F : ℝ)| / (Module.finrank ℚ c.F : ℝ) :=
  fun hMass hTor D j H Dw l Xo c U dict hL _ χ hχ a n hD hG h0 =>
    GlobalTheory.LamMuMax.slopeMax_le_of_bounds D j H Dw l Xo c U dict a n _ _ hG h0
      (fun F hF hF0 => (UpperTheory.Lit.Tam.petersson_norm_tamagawa_formula hMass hTor D j H Dw l Xo c U dict hL χ hχ a n hD F hF hF0).2)
      (UpperTheory.Lit.Tam.finrank_cuspW_le_supConst2 hMass hTor D j H Dw l Xo c U dict hL a n hD)

theorem UpperTheory.Lit.Tam.holSub_supE_sq_le_supConst2_mul_petE_sq :
    True → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E)
      (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l)
      (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
      (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r),
      Laws D j Xo c U dict → ∀ σ, GoodEmb c σ →
      ∀ (la : ∀ k, Wt ((U σ).X k).Ψ D.R.r) (w : ℝ), 0 < w →
      (∀ k, (∑ τ, ((U σ).X k).spread (la k) τ) ≤ w) →
      (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (la k) γ = 1) →
      ∀ P ∈ holSub (U σ).X la,
        supE (U σ).X la P ^ 2 ≤
          ENNReal.ofReal (MainStatements.Tam.Plug.supConst2 D.host.E D.R.r D.host.d l.M w) *
            petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 :=
  fun _ => UpperTheory.Lit.Tam.tamagawa_local_volume_factor trivial GlobalTheory.T.normOneTorusClassNumberBound_proof

theorem UpperTheory.Lit.Tam.tamagawa_measure_comparison :
    True → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E)
      (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l)
      (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
      (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r),
      Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d),
      GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n →
      GoodW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) → latW U (wtZ a n) ≠ ⊥ →
      slopeMax_sq (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n)) (latW U (wtZ a n)) ≤
        2 * lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re
            ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) +
          2 * Real.log (MainStatements.Tam.Plug.supConst2 D.host.E D.R.r D.host.d l.M
            (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1)) +
          Real.log |(discr c.F : ℝ)| / (Module.finrank ℚ c.F : ℝ) :=
  fun _ => UpperTheory.Lit.Tam.petersson_norm_local_factor_eq trivial GlobalTheory.T.normOneTorusClassNumberBound_proof

end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
  Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal
  GlobalTheory.DegCmp GlobalTheory.BadCount
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

theorem UpperTheory.Lit.Tam.tamagawaPeterssonLambdaSq_nonneg :
    True → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E)
      (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
      (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
      (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ D.R.r),
      GlobalTheory.LevGeo.Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (G : WTZ D.host.E), Even G.2 →
      ∀ (w : ℝ), 0 < w → (∀ k, (∑ τ, ((U σ).X k).spread (AllWt.modelWt (U σ) G k) τ) ≤ w) →
      ∀ (Z : Comp Xo c) (y : FPt (U σ).X),
        (⟨y.1, y.2.1⟩ : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ D.R.r) ∈ AllWt.framesOn (U σ) Z →
        AllWt.bergOn (U σ) (D.sp.W j) (dict σ) Z G y ≤
          ENNReal.ofReal (MainStatements.Tam.Plug.supConst2 D.host.E D.R.r D.host.d l.M w) :=
  fun hT D j H Dw l Xo c U dict hL σ hσ G hG w hw hsp Z y hy =>
    GlobalTheory.BergComp.bergOn_le_of_sup D j H Dw l Xo c U dict hL σ hσ G hG _
      (UpperTheory.Lit.Tam.holSub_supE_sq_le_supConst2_mul_petE_sq hT D j H Dw l Xo c U dict hL σ hσ
        (AllWt.modelWt (U σ) G) w hw hsp (GlobalTheory.AllWt.Model.chi_modelWt (U σ) (hL.chiTriv σ hσ) G hG))
      Z y hy

/-- Sharper quadratic-in-`(f, r)`, linear-in-`Lb` bound for `MainStatements.Tam.Plug.supConst2`. -/
theorem UpperTheory.Lit.Tam.supConst2_log_le_quadratic (D : D7) (M : ℕ) (Lb w : ℝ)
    (hM : 1 ≤ M) (hLb : 1 ≤ Lb) (hMl : Real.log M ≤ 30 * Lb) (hsz : fieldSz D.host.E ≤ 3 * Lb)
    (hfrl : Real.log (D.R.f * D.R.r) ≤ Lb) (hw : 1 ≤ w) (hwl : Real.log w ≤ 25 * Lb) :
    1 ≤ MainStatements.Tam.Plug.supConst2 D.host.E D.R.r D.host.d M w ∧
      Real.log (MainStatements.Tam.Plug.supConst2 D.host.E D.R.r D.host.d M w) ≤
        3125 * ((D.R.f : ℝ) * D.R.r) ^ 2 * Lb :=
  GlobalTheory.ConstSzRows.supConst_quadratic_rows D M Lb w _ hM hLb hMl hsz hfrl hw hwl
    fun L => MainStatements.Tam.Plug.supremum_constant_log_bound_alt D.host.E D.R.r D.host.d M w L

theorem UpperTheory.Lit.Tam.supConst2Bounds :
    ∀ (D : D7) (M : ℕ) (Lb w : ℝ), 1 ≤ M → 1 ≤ Lb → Real.log M ≤ 30 * Lb →
      fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → 1 ≤ w → Real.log w ≤ 25 * Lb →
      1 ≤ MainStatements.Tam.Plug.supConst2 D.host.E D.R.r D.host.d M w ∧
        Real.log (MainStatements.Tam.Plug.supConst2 D.host.E D.R.r D.host.d M w) ≤
          4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 :=
  fun D M Lb w hM hLb hMl hsz hfrl hw hwl =>
    GlobalTheory.ConstSzRows.supConst_size_rows_of_log_bound D M Lb w _ hM hLb hMl hsz hfrl hw hwl
      fun L => MainStatements.Tam.Plug.supremum_constant_log_bound_alt D.host.E D.R.r D.host.d M w L

theorem UpperTheory.Lit.Tam.tamagawa_weight_bound :
    Hypotheses2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ,
      1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j →
      ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb →
      Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb →
      o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) →
      Real.log (∑ τ, ∑ k, |(la τ k : ℝ)|) ≤ 20 * Lb → ∀ Z,
        BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la (Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) ∧
          SupBdWt Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z la (Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) ∧
          Real.log (Y.rkC la Z) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 :=
  fun _ => ⟨4000, by norm_num, fun D T hT j _ _ _ hj Y e o hY Lb hLb hM hsz hfr _ la _ hS Z =>
    GlobalTheory.BergRank.berg_sup_rank_of_const D T hT j hj Y e o hY Lb hLb hsz la hS Z
      (MainStatements.Tam.Plug.supConst2 D.host.E D.R.r D.host.d Y.d.l₂.M)
      (fun w hw1 hlw => UpperTheory.Lit.Tam.supConst2Bounds D Y.d.l₂.M Lb w
        (by have := Y.d.l₂.three_le; omega) hLb hM hsz hfr hw1 hlw)
      (fun hL w hw hsp σ hσ y hy => UpperTheory.Lit.Tam.tamagawaPeterssonLambdaSq_nonneg trivial D j _ _ _ _ _
        Y.U Y.dict hL σ hσ (wtOf _ la 0) (AllWt.even_wtOf la 0) w hw (hsp σ hσ) Z y hy)⟩

end

section
set_option synthInstance.maxHeartbeats 400000

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV
  Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
  GlobalTheory.CovTop

namespace GlobalTheory.CovTop.LamCore

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
  {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
  (p : PtAt ex Csz) (i : Fin D.R.m)

theorem _root_.UpperTheory.Lit.Tam.slopeMax_sq_latW_le_pow_mul (h6 : True) {PP A : ℝ}
    (hR : RecTied D L) (hG : GramAt p i) (hN : HostNum D L PP A 1) (hW : WtNum p i PP) :
    slopeMax_sq (nrmK p.fw i) (latW (p.T.U ((i : ℕ) + 1)) (Gk p i)) ≤ L.sc.x ^ (2 * A + 4) * L.sc.b :=
  slopeMax_le_of_const p i hR hG hN hW (MainStatements.Tam.Plug.supConst2 D.host.E D.R.r D.host.d)
    (fun hLaws _ χ hχ hgood => UpperTheory.Lit.Tam.tamagawa_measure_comparison h6 D _ _ _ _ _ _ _ _
      hLaws χ hχ (wtA (p.κ i)) (p.κ i).n hW.dom hgood (latW_ne_bot p i hG))
    (fun M w L' hr2 hd hM hL' hw hl1 hlM hl2 hl3 hlw =>
      (MainStatements.Tam.Plug.supremum_constant_log_bound_alt D.host.E D.R.r D.host.d M w L' hr2 hd hM hL' hw
        hl1 hlM hl2 hl3 hlw).2)

theorem _root_.UpperTheory.Lit.Tam.integral_cusp_slope_power_bound :
    Hypotheses2 → Gram → Lifts fun Fm x _ ι p i _ A =>
      slopeMax_sq (nrmK p.fw i) (latW (p.T.U ((i : ℕ) + 1)) (Gk p i)) ≤ (Fm.L x ι).sc.x ^ A * (Fm.L x ι).sc.b := by
  intro hP hG
  refine Closed.imp (Closed.and hG (Closed.and (GlobalTheory.CovTop.Sizes.hostN 1) GlobalTheory.T.weight_bound_holds)) ?_
  rintro eps Fm CH - ⟨⟨_, -, h1⟩, ⟨A, hA, h2⟩, ⟨_, -, h3⟩⟩
  obtain ⟨x0, h⟩ := h1.and (h2.and h3)
  refine ⟨2 * A + 4, by linarith, x0, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨a, b, c⟩ := h x hx hle ι p hp
  exact UpperTheory.Lit.Tam.slopeMax_sq_latW_le_pow_mul p i trivial hp.2 (a i) (b i) (c i)

end GlobalTheory.CovTop.LamCore
end
end
