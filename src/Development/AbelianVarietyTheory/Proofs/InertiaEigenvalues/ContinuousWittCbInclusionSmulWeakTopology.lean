module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfTailStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousZlSmulStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowInclRSmulMemStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearMapPiContinuousCoordStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.WeakClosed

theorem continuous_io_smul_of {O RA RW M : Type} [CommRing O] [TopologicalSpace O] [CommRing RA]
    [Algebra O RA] [CommRing RW] [Algebra O RW] [AddCommGroup M] [Module RW M] [Module O M]
    [IsScalarTower O RW M] [TopologicalSpace M] [IsTopologicalAddGroup M] {n : ℕ}
    (io : LetA O n →ₐ[O] RA) (inc : RA →ₐ[O] RW) (y : M) (πA : RA) (hπ : io letπ = πA)
    (hsmall : ∀ U ∈ 𝓝 (0 : M), ∃ k : ℕ, ∀ z : RA, inc (πA ^ k * z) • y ∈ U)
    (hlin : ∀ f : (ZMod n → O) →ₗ[O] M, Continuous f) :
    Continuous fun a : LetA O n => inc (io a) • y := by
  let Φ : LetA O n →+ M :=
    { toFun := fun a => inc (io a) • y
      map_zero' := by simp
      map_add' := fun a c => by simp [add_smul] }
  refine GlobalTheory.T.continuous_of_tail_small_of_monomial_continuous Φ ?_ ?_
  · intro U hU
    obtain ⟨k, hk⟩ := hsmall U hU
    refine ⟨k, fun r => ?_⟩
    have hΦ : Φ (letπ ^ k * r) = inc (πA ^ k * io r) • y := by
      show inc (io (letπ ^ k * r)) • y = _
      rw [map_mul, map_pow, hπ]
    rw [hΦ]
    exact hk _
  · intro j
    let f : (ZMod n → O) →ₗ[O] M :=
      { toFun := fun c => inc (io (fun i => PowerSeries.C (c i))) • (inc (io letπ) ^ j • y)
        map_add' := fun c c' => by
          have : (fun i => PowerSeries.C ((c + c') i)) =
              (fun i => PowerSeries.C (c i)) + fun i => PowerSeries.C (c' i) := by
            funext i; simp
          simp only [this, map_add (f := _), add_smul]
        map_smul' := fun o c => by
          have : (fun i => PowerSeries.C ((o • c) i)) = o • (fun i => PowerSeries.C (c i)) := by
            funext i; simp [PowerSeries.smul_eq_C_mul, map_mul]
          simp only [this, map_smul, smul_assoc, RingHom.id_apply] }
    refine (hlin f).congr fun c => ?_
    have hc : (fun i => PowerSeries.C (c i) * PowerSeries.X ^ j : LetA O n) =
        (fun i => PowerSeries.C (c i)) * letπ ^ j := by
      funext i; simp [letπ]
    show inc (io (fun i => PowerSeries.C (c i))) • (inc (io letπ) ^ j • y) =
      inc (io (fun i => PowerSeries.C (c i) * PowerSeries.X ^ j)) • y
    rw [hc, map_mul, map_mul, mul_smul, map_pow, map_pow]

end GlobalTheory.WeakClosed

namespace GlobalTheory.WeakClosed

theorem isTopologicalAddGroup_twTop {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (T : Lt K LL) {d : ℕ}
    (b : LatB T d) : letI := twTop T b; IsTopologicalAddGroup (TW (RW LL) T) := by
  letI := cbValued l
  letI := zlMod T
  haveI := zlTower T
  letI : TopologicalSpace (WCb l) := wTop l
  letI : TopologicalSpace (TW (RW LL) T) := twTop T b
  haveI : IsTopologicalRing (Cb l) := inferInstance
  haveI : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  exact Topology.IsInducing.topologicalAddGroup (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b) ⟨rfl⟩

theorem finrank_maxUnramifiedSubfield_pos {l : ℕ} [Fact l.Prime] (K : FinExt l) : 0 < Module.finrank ℚ_[l] ↥(K0 K) := by
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] (K0 K) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (RingHom.injective _)
  exact Module.finrank_pos

theorem continuous_inclR_io_smul : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l} {h : Good K s LL} {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))} (E : EtSit P AI K s LL h W) (T : Lt K LL) {d e : ℕ} (b : LatB T d) (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)) (y : TW (RW LL) T), letI := twTop T b; letI := aTop (K := K) bO; Continuous fun a : AA K LL => inclR LL (E.tie.io a) • y := by
  intro l _ P AI K s LL h W E T d e b bO y
  letI tT : TopologicalSpace (TW (RW LL) T) := twTop T b
  letI tO : TopologicalSpace ↥(OL LL) := oTop bO
  haveI := isTopologicalAddGroup_twTop T b
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨(finrank_maxUnramifiedSubfield_pos K).ne'⟩
  have hlin : ∀ f : (ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL)) →ₗ[↥(OL LL)] TW (RW LL) T,
      Continuous f := fun f => GlobalTheory.T.continuous_linearMap_pi_of_continuous_coord bO (GlobalTheory.T.continuous_padicInt_smul_latB T b) f
  haveI : IsScalarTower ↥(OL LL) (RW LL) (TW (RW LL) T) :=
    TensorProduct.isScalarTower_left (R := ↥(OL LL)) (M := RW LL) (N := ↥T.L.T)
      (R' := RW LL) (R'₂ := ↥(OL LL))
  exact continuous_io_smul_of E.tie.io (inclR LL) y _ E.tie.io_π (GlobalTheory.T.exists_pow_inclR_smul_mem' AI s T b y) hlin

end GlobalTheory.WeakClosed
