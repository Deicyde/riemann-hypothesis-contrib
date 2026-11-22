module

public import Development.WeilBound.ThetaLifts.Reductions.HasDerivAtSchwartzToL2
public import CompanionTheory.ThickeningEstimates.InnerProductFactorization.EqOfInner

@[expose] public section

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology
open scoped Real

namespace CompanionTheory.ThKR.LL

variable {l : Type} [Fintype l]

theorem exists_decay {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : SchwartzMap (EuclideanSpace ℝ l) F) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, (1 + ‖x‖) ^ k * ‖g x‖ ≤ C := by
  have h := fun x => one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0) le_rfl le_rfl g x
  simp only [norm_iteratedFDeriv_zero] at h
  exact ⟨_, le_trans (by positivity) (h 0), h⟩

theorem csmul (r : ℝ) (x : L2 l) : (r : ℂ) • x = r • x := by
  rw [coe_smul]
  rfl

theorem hasDerivAt_schwartz_to_L2 {F : ℝ → Sch l} {G : Sch l} {t₀ : ℝ} (hp : ∀ x, HasDerivAt (fun t => F t x) (G x) t₀) {C : ℝ}
    (hb : ∀ᶠ t in 𝓝 t₀, ∀ x, (1 + ‖x‖) ^ (Module.finrank ℝ (EuclideanSpace ℝ l) + 1) * ‖F t x - F t₀ x‖ ≤ C * |t - t₀|) :
    HasDerivAt (fun t => schwartzToL2 l (F t)) (schwartzToL2 l G) t₀ := by
  exact PositivityTheory.ThKR.LL.hasDerivAt_schwartz_to_L2 hp hb

def LD (U : ℝ → Sch l →L[ℂ] Sch l) (Q : Sch l → Sch l) (t₀ : ℝ) : Prop :=
  ∀ f, HasDerivAt (fun t => schwartzToL2 l (U t f)) (schwartzToL2 l (Q f)) t₀

theorem LD.const (U : Sch l →L[ℂ] Sch l) (t₀ : ℝ) : LD (fun _ => U) (fun _ => 0) t₀ := fun f => by
  simpa using hasDerivAt_const t₀ (schwartzToL2 l (U f))

theorem LD.smul {U : ℝ → Sch l →L[ℂ] Sch l} {Q : Sch l → Sch l} {t₀ : ℝ} (h : LD U Q t₀) {c : ℝ → ℂ} {c' : ℂ}
    (hc : HasDerivAt c c' t₀) : LD (fun t => c t • U t) (fun f => c t₀ • Q f + c' • U t₀ f) t₀ := fun f => by
  simpa using hc.fun_smul (h f)

theorem LD.mul {U W : ℝ → Sch l →L[ℂ] Sch l} {P Q : Sch l → Sch l} {t₀ : ℝ} (hU : LD U P t₀) (hW : LD W Q t₀)
    (hn : ∀ᶠ t in 𝓝 t₀, ∀ f, ‖schwartzToL2 l (U t f)‖ = ‖schwartzToL2 l f‖) :
    LD (fun t => U t * W t) (fun f => P (W t₀ f) + U t₀ (Q f)) t₀ := fun f => by
  have h1 : HasDerivAt (fun t => schwartzToL2 l (U t (W t f - W t₀ f - ((t - t₀ : ℝ) : ℂ) • Q f))) 0 t₀ := by
    have h := (hW f).isLittleO
    rw [hasDerivAt_iff_isLittleO]
    refine Asymptotics.IsBigO.trans_isLittleO (Asymptotics.IsBigO.of_bound 1 ?_) h
    filter_upwards [hn] with t ht
    simp only [sub_self, ofReal_zero, zero_smul, map_zero, smul_zero, sub_zero, ht, one_mul]
    simp only [map_sub, map_smul]
    simp only [csmul, le_refl]
  have h2 : HasDerivAt (fun t : ℝ => (t - t₀) • schwartzToL2 l (U t (Q f))) (schwartzToL2 l (U t₀ (Q f))) t₀ := by
    simpa using ((hasDerivAt_id t₀).sub_const t₀).fun_smul (hU (Q f))
  have h3 := (h1.fun_add h2).fun_add (hU (W t₀ f))
  rw [zero_add, ← map_add (f := _), add_comm (U t₀ (Q f))] at h3
  refine h3.congr_of_eventuallyEq (.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.mul_apply, map_sub, map_smul]
  simp only [csmul]
  abel

variable [DecidableEq l]

end CompanionTheory.ThKR.LL
