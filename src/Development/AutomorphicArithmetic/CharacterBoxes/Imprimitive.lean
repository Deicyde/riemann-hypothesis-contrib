module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.HC

theorem UpperTheory.Top.imprimitive :
    ZeroFreeAll → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
      DirichletCharacter.LFunction χ s ≠ 0 := by
  intro h N _ χ s hs hχs
  haveI : NeZero χ.conductor := (PChar.of χ).ne
  have hL : DirichletCharacter.LFunction χ.primitiveCharacter s ≠ 0 := h (PChar.of χ) trivial s hs
  have hχ' : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := by
    rcases hχs with hχ | hs1
    · left
      intro h1
      apply hχ
      rw [← χ.changeLevel_primitiveCharacter, h1, DirichletCharacter.changeLevel_one]
    · exact Or.inr hs1
  have hrw := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter hχ'
  rw [χ.changeLevel_primitiveCharacter] at hrw
  rw [hrw]
  refine mul_ne_zero hL (Finset.prod_ne_zero_iff.mpr fun p hp => ?_)
  have hp' := Nat.prime_of_mem_primeFactors hp
  intro h0
  have key : χ.primitiveCharacter p * (p : ℂ) ^ (-s) = 1 := by linear_combination -h0
  have h1 : ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
  have h2 : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp'.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp'.one_lt) (by linarith)
  have hn : ‖χ.primitiveCharacter p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ * ‖(p : ℂ) ^ (-s)‖
        ≤ 1 * ‖(p : ℂ) ^ (-s)‖ := by gcongr
      _ < 1 := by simpa using h2
  rw [key, norm_one] at hn
  exact lt_irrefl _ hn
