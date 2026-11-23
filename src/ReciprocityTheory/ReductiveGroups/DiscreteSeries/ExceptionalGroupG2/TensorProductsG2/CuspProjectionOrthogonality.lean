module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.ContinuousUnitaryMatrix
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CuspProjectionOrthogonality

@[expose] public section

noncomputable section

open Finset MeasureTheory
open scoped ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

section Psi

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

theorem continuous_spherical_psi (hP : IsPsiFor ε lam T Ψ) :
    Continuous (fun g : Formalism.REAL.UJ ε => Ψ (Formalism.MainNotions.S.umat g)) :=
  (ffa_continuousOn hP.2.2.1).comp_continuous continuous_umat' (fun g => g.2)

theorem psi_twist_coef_memLp (dual : Bool) (hP : IsPsiFor ε lam T Ψ)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε)) (ξ ζ : Fin n → T.V) :
    MemLp (fun g : Formalism.REAL.UJ ε => ob2PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
  simp_rw [psi_coef_expand]
  refine memLp_finsetSum _ fun c _ => memLp_finsetSum _ fun d _ => ?_
  refine (hWT (ζ d) (ξ c)).of_le ?_ (Filter.Eventually.of_forall fun g => ?_)
  · exact ((continuous_tensor_phi dual c d).mul (continuous_const.inner
      ((continuous_spherical_psi hP).clm_apply continuous_const))).aestronglyMeasurable
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right (norm_tensor_phi_le_sqrt_hs g.2 dual c d) (norm_nonneg _)

theorem psi_term_integrable (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε)) (ξ ζ : Fin n → T.V) (u v : T'.V) :
    Integrable (fun g : Formalism.REAL.UJ ε => starRingEnd ℂ (ob2PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) *
      inner ℂ u (Ψ' (Formalism.MainNotions.S.umat g) v)) (Formalism.REAL.muG ε) := by
  have h1 := (psi_twist_coef_memLp dual hP hWT ξ ζ).star
  have h2 : MemLp (fun g : Formalism.REAL.UJ ε => inner ℂ u (Ψ' (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε) :=
    memLp_muG_of_haar ε (fun x => inner ℂ u (Ψ' x v)) 2
      (fun μ hμ => (pdA_coef u v).comp_memLp' (hP'.2.2.2.2 μ hμ))
  exact h1.integrable_mul h2

end Psi

section Main

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

theorem continuous_psi_pairing_sum (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V)) :
    Continuous (fun g : Formalism.REAL.UJ ε => ∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g) := by
  have h1 := continuous_spherical_psi hP
  have h2 := continuous_spherical_psi hP'
  have h3 := continuous_tensor_phi (ε := ε) dual
  simp only [ob2Fij, psi_coef_expand]
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (Complex.continuous_conj.comp (continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun d _ =>
      (h3 c d).mul (continuous_const.inner (h1.clm_apply continuous_const)))).mul
      (continuous_const.inner (h2.clm_apply continuous_const))

theorem psi_pairing_trace_pos (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (hpos : ∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive)
    (hpos' : ∀ X, inP ε X → (Ψ' (NormedSpace.exp X)).IsPositive)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε))
    (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V)) (hι₀ : ι₀ ≠ 0)
    (hK : ∀ (k : S7.KG ε) (v : T'.V), ι₀ (T'.op k v) = ob2TauF dual T k (ι₀ v)) :
    0 < (∑ i, ∑ j, ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (ob2PsiCoef dual Ψ (ι₀ (stdOrthonormalBasis ℂ T'.V i)) (ι₀ (stdOrthonormalBasis ℂ T'.V j))
        (Formalism.MainNotions.S.umat g)) *
      inner ℂ (stdOrthonormalBasis ℂ T'.V i) (Ψ' (Formalism.MainNotions.S.umat g) (stdOrthonormalBasis ℂ T'.V j))
        ∂(Formalism.REAL.muG ε)).re := by
  show 0 < (∑ i, ∑ j, ∫ g, ob2Fij dual Ψ Ψ' ι₀ i j g ∂(Formalism.REAL.muG ε)).re
  have hint : ∀ i j, Integrable (ob2Fij dual Ψ Ψ' ι₀ i j) (Formalism.REAL.muG ε) := fun i j =>
    psi_term_integrable dual hP hP' hWT _ _ _ _
  have hFi : Integrable (fun g => ∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g) (Formalism.REAL.muG ε) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j
  have hsum : ∫ g, (∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g) ∂(Formalism.REAL.muG ε) =
      ∑ i, ∑ j, ∫ g, ob2Fij dual Ψ Ψ' ι₀ i j g ∂(Formalism.REAL.muG ε) := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hint i j
  rw [← hsum]
  have hre : (∫ g, (∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g) ∂(Formalism.REAL.muG ε)).re =
      ∫ g, (∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g).re ∂(Formalism.REAL.muG ε) :=
    (integral_re hFi).symm
  rw [hre]
  have hG0 : 0 ≤ fun g : Formalism.REAL.UJ ε => (∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g).re := by
    intro g
    have h := psi_pairing_nonneg dual hP hP' hpos hpos' ι₀ hK (g := Formalism.MainNotions.S.umat g) g.2
    have h' := (Complex.le_def.mp h).1
    rw [Complex.zero_re] at h'
    exact h'
  have hGc : Continuous fun g : Formalism.REAL.UJ ε => (∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g).re :=
    Complex.continuous_re.comp (continuous_psi_pairing_sum dual hP hP' ι₀)
  rw [integral_pos_iff_support_of_nonneg hG0 hFi.re]
  exact hGc.isOpen_support.measure_pos _ ⟨1, Function.mem_support.mpr (psi_pairing_at_one_re_pos dual hP hP' ι₀ hι₀).ne'⟩

end Main

end ReciprocityTheory.ChartRestriction.DS.G2
