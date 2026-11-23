module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

namespace GroundTheory.Automorphic

namespace Whittaker

open Finset

variable {n : ℕ} {w : Equiv.Perm (Fin n)}

theorem val_eq_of_le_of_le
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) :
    ∀ (g : ℕ) (z y : Fin n), (w y).val = (w z).val + g → z ≤ y →
      ∀ x : Fin n, z ≤ x → x ≤ y → (w x).val = (w z).val + (x.val - z.val) := by
  intro g
  induction g with
  | zero =>
    intro z y hgap hzy x hzx hxy
    have hyz : y = z := w.injective (Fin.ext (by simpa using hgap))
    subst y
    obtain rfl := le_antisymm hxy hzx
    simp
  | succ g ih =>
    intro z y hgap hzy x hzx hxy
    have hlt : (w z).val + 1 < n := by
      have := (w y).isLt
      omega
    let p := w.symm ⟨(w z).val + 1, hlt⟩
    have hwp : (w p).val = (w z).val + 1 := by simp [p]
    have hpy : (w y).val = (w p).val + g := by omega
    obtain hpz | hzp := le_or_gt p z
    · have := ih p y hpy (hpz.trans hzy) z hpz hzy
      omega
    · have hp := hB z p hzp hwp
      obtain rfl | hzx := hzx.eq_or_lt
      · simp
      · have hpx : p.val ≤ x.val := hp.symm ▸ Fin.lt_def.mp hzx
        have := ih p y hpy (le_trans (Fin.le_def.mpr hpx) hxy) x hpx hxy
        omega

theorem val_eq_of_le_right
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) (b x : Fin n)
    (hbx : b ≤ x) (hx : x.val ≤ b.val + #(univ.filter fun y : Fin n => b < y ∧ w b < w y)) :
    (w x).val = (w b).val + (x.val - b.val) := by
  set R := univ.filter fun y : Fin n => b < y ∧ w b < w y with hR
  by_cases hne : R.Nonempty
  · set m := R.max' hne
    have hm : m ∈ R := R.max'_mem hne
    rw [hR, mem_filter] at hm
    have hsub : R ⊆ Ioc b m := by
      intro y hy
      have hy' := hy
      rw [hR, mem_filter] at hy'
      exact mem_Ioc.2 ⟨hy'.2.1, R.le_max' y hy⟩
    have hcard : #R ≤ m.val - b.val := by
      have := card_le_card hsub
      rwa [Fin.card_Ioc] at this
    exact val_eq_of_le_of_le hB ((w m).val - (w b).val) b m (by omega) (le_of_lt hm.2.1) x hbx
      (Fin.le_iff_val_le_val.2 (by omega))
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, card_empty] at hx
    have : x = b := Fin.ext (by rw [Fin.le_iff_val_le_val] at hbx; omega)
    subst this
    simp

theorem val_add_eq_of_le_left
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) (b x : Fin n)
    (hxb : x ≤ b) (hx : b.val ≤ x.val + #(univ.filter fun y : Fin n => y < b ∧ w y < w b)) :
    (w x).val + (b.val - x.val) = (w b).val := by
  set L := univ.filter fun y : Fin n => y < b ∧ w y < w b with hL
  by_cases hne : L.Nonempty
  · set m := L.min' hne
    have hm : m ∈ L := L.min'_mem hne
    rw [hL, mem_filter] at hm
    have hsub : L ⊆ Ico m b := by
      intro y hy
      have hy' := hy
      rw [hL, mem_filter] at hy'
      exact mem_Ico.2 ⟨L.min'_le y hy, hy'.2.1⟩
    have hcard : #L ≤ b.val - m.val := by
      have := card_le_card hsub
      rwa [Fin.card_Ico] at this
    have h1 := val_eq_of_le_of_le hB ((w b).val - (w m).val) m b (by omega) (le_of_lt hm.2.1) x
      (Fin.le_iff_val_le_val.2 (by omega)) hxb
    have h2 := val_eq_of_le_of_le hB ((w b).val - (w m).val) m b (by omega) (le_of_lt hm.2.1) b
      (le_of_lt hm.2.1) le_rfl
    rw [Fin.le_iff_val_le_val] at hxb
    omega
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, card_empty] at hx
    have : x = b := Fin.ext (by rw [Fin.le_iff_val_le_val] at hxb; omega)
    subst this
    simp

theorem card_filter_lt_apply (w : Equiv.Perm (Fin n)) (b : Fin n) :
    #(univ.filter fun x : Fin n => w x < w b) = (w b).val := by
  have : (univ.filter fun x : Fin n => w x < w b) = (Iio (w b)).map w.symm.toEmbedding := by
    ext x
    simp [mem_map_equiv]
  rw [this, card_map, Fin.card_Iio]

theorem val_add_card_right (w : Equiv.Perm (Fin n)) (b : Fin n) :
    (w b).val + #(univ.filter fun y : Fin n => b < y ∧ w b < w y) =
      #(univ.filter fun y : Fin n => y < b ∧ w y < w b) + (n - 1 - b.val) := by
  -- Both sides count the union of the positions above b and the preimages below w b.
  let L := univ.filter fun y : Fin n => w y < w b
  have hright : (univ.filter fun y : Fin n => b < y ∧ w b < w y) = Ioi b \ L := by
    ext y
    simp only [L, mem_filter, mem_univ, true_and, mem_sdiff, mem_Ioi, not_lt]
    exact and_congr_right fun hy => ⟨fun h => h.le, fun h => h.lt_of_ne (w.injective.ne hy.ne)⟩
  have hleft : (univ.filter fun y : Fin n => y < b ∧ w y < w b) = L \ Ioi b := by
    ext y
    simp only [L, mem_filter, mem_univ, true_and, mem_sdiff, mem_Ioi, not_lt]
    rw [and_comm]
    exact and_congr_right fun hw =>
      ⟨fun h => h.le, fun h => h.lt_of_ne (fun e => hw.ne (congrArg w e))⟩
  rw [← card_filter_lt_apply w b, ← Fin.card_Ioi b, hright, hleft, Nat.add_comm _ #(Ioi b \ L),
    card_sdiff_add_card, card_sdiff_add_card, union_comm]

theorem relevant_involution
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) (b : Fin n) :
    w (Fin.rev (w b)) = Fin.rev b := by
  have hid := val_add_card_right w b
  set r := #(univ.filter fun y : Fin n => b < y ∧ w b < w y)
  set l := #(univ.filter fun y : Fin n => y < b ∧ w y < w b)
  set c := Fin.rev (w b) with hc
  have hcv : c.val = n - (↑(w b) + 1) := by rw [hc, Fin.val_rev]
  have hb := b.isLt
  apply Fin.ext
  rw [Fin.val_rev]
  by_cases hcb : b.val ≤ c.val
  · have := val_eq_of_le_right hB b c (Fin.le_iff_val_le_val.2 hcb) (by omega)
    omega
  · have := val_add_eq_of_le_left hB b c (Fin.le_iff_val_le_val.2 (by omega)) (by omega)
    omega

/-- The torus coordinate is constant between any two positions in increasing image order. -/
private theorem apply_eq_of_le_of_apply_le {α : Type*} (t : Fin n → α)
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1)
    (ht : ∀ (i : Fin n) (h : i.val + 1 < n), w i < w ⟨i.val + 1, h⟩ →
      t (w i) = t (w ⟨i.val + 1, h⟩))
    {a b : Fin n} (hab : a ≤ b) (hw : w a ≤ w b) : t (w a) = t (w b) := by
  have hval := val_eq_of_le_of_le hB ((w b).val - (w a).val) a b
    (Nat.add_sub_of_le (Fin.le_def.mp hw)).symm hab
  have run (j : ℕ) (haj : a.val ≤ j) (hjb : j ≤ b.val) :
      t (w a) = t (w ⟨j, hjb.trans_lt b.isLt⟩) := by
    induction j, haj using Nat.le_induction with
    | base => rfl
    | succ j haj ih =>
      have hj : j < b.val := hjb
      let i : Fin n := ⟨j, hj.trans b.isLt⟩
      refine (ih hj.le).trans (ht i (hjb.trans_lt b.isLt) ?_)
      rw [Fin.lt_def, hval i haj hj.le,
        hval ⟨j + 1, hjb.trans_lt b.isLt⟩ (Nat.le_succ_of_le haj) hjb]
      change (w a).val + (j - a.val) < (w a).val + (j + 1 - a.val)
      omega
  exact run b.val hab le_rfl

theorem apply_eq_of_run_right {α : Type*} (t : Fin n → α)
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1)
    (ht : ∀ (i : Fin n) (h : i.val + 1 < n), w i < w ⟨i.val + 1, h⟩ →
      t (w i) = t (w ⟨i.val + 1, h⟩))
    (b : Fin n) :
    ∀ k : ℕ, ∀ x : Fin n, x.val = b.val + k →
      k ≤ #(univ.filter fun y : Fin n => b < y ∧ w b < w y) → t (w x) = t (w b) := by
  intro k x hx hk
  have hbx : b.val ≤ x.val := by omega
  have h := val_eq_of_le_right hB b x hbx (by omega)
  have hw : w b ≤ w x := Fin.le_def.mpr (by omega)
  exact (apply_eq_of_le_of_apply_le t hB ht hbx hw).symm

theorem apply_eq_of_run_left {α : Type*} (t : Fin n → α)
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1)
    (ht : ∀ (i : Fin n) (h : i.val + 1 < n), w i < w ⟨i.val + 1, h⟩ →
      t (w i) = t (w ⟨i.val + 1, h⟩))
    (b : Fin n) :
    ∀ k : ℕ, ∀ x : Fin n, x.val + k = b.val →
      k ≤ #(univ.filter fun y : Fin n => y < b ∧ w y < w b) → t (w x) = t (w b) := by
  intro k x hx hk
  have hxb : x.val ≤ b.val := by omega
  have h := val_add_eq_of_le_left hB b x hxb (by omega)
  have hw : w x ≤ w b := Fin.le_def.mpr (by omega)
  exact apply_eq_of_le_of_apply_le t hB ht hxb hw

theorem relevant_torus {α : Type*} (t : Fin n → α)
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1)
    (ht : ∀ (i : Fin n) (h : i.val + 1 < n), w i < w ⟨i.val + 1, h⟩ →
      t (w i) = t (w ⟨i.val + 1, h⟩))
    (b : Fin n) : t (w b) = t (Fin.rev b) := by
  have hinv := relevant_involution hB b
  rw [← hinv]
  obtain h | h := le_total b (Fin.rev (w b))
  · apply apply_eq_of_le_of_apply_le t hB ht h
    rwa [hinv, Fin.le_rev_iff]
  · symm
    apply apply_eq_of_le_of_apply_le t hB ht h
    rwa [hinv, Fin.rev_le_iff]

end Whittaker

end GroundTheory.Automorphic
