module

public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsIsoOfGenerators
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo Formalism.MainNotions.LocalSituation TensorProduct

variable {l : ℕ} [Fact l.Prime]

theorem zl_WCb_injective : Function.Injective (algebraMap ℤ_[l] (WCb l)) := by
  change Function.Injective (zlW l (Cb l))
  unfold zlW
  rw [RingHom.coe_comp]
  exact (WittVector.map_injective _ (ZMod.castHom (dvd_refl l) (Cb l)).injective).comp
    (WittVector.equiv l).symm.injective

theorem zl_LL_injective (LL : FinExt l) : Function.Injective (algebraMap ℤ_[l] ↥LL.1) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1, RingHom.coe_comp]
  exact (algebraMap ℚ_[l] ↥LL.1).injective.comp (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l])

instance tfLL (LL : FinExt l) : Module.IsTorsionFree ℤ_[l] ↥LL.1 :=
  Module.isTorsionFree_iff_algebraMap_injective.2 (zl_LL_injective LL)

theorem O_RW_injective (LL : FinExt l) : Function.Injective (algebraMap ↥(OL LL) (RW LL)) := by
  have h := Algebra.TensorProduct.includeLeft_injective (R := ℤ_[l]) (A := ↥(OL LL)) (B := WCb l)
    (S := ↥(OL LL)) zl_WCb_injective
  convert h using 1
  funext x
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem oneT_inj_gen {G : Type} [Group G] [TopologicalSpace G] (LL : FinExt l)
    (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) :
    Function.Injective (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) := by
  have hF : Module.Free ↥(OL LL) ↥T.L.T := T.L.free
  have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T)
    (Algebra.linearMap ↥(OL LL) (RW LL)) (O_RW_injective LL)
  have h2 := h1.comp (TensorProduct.lid ↥(OL LL) ↥T.L.T).symm.injective
  convert h2 using 1
  funext t
  simp [Algebra.TensorProduct.one_def]

theorem oneInj_sit (LT : LocTheory) (HW : HWOf LT) (AI : LocAinf l (LT l)) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) : OneInj (sit LT HW l AI K s LL h) :=
  fun T => oneT_inj_gen (G := ↥(GK K)) LL T

end Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators
