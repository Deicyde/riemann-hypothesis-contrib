module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.MassLev2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupremumConstantLogBound
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ConstantSupremum.Imports
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

namespace MainStatements.Tam.Plug

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

def supConst2 (E : Type) [Field E] [NumberField E] (r d M : ℕ) (w : ℝ) : ℝ :=
  locConst E r w (epsLev E d M w) * MainStatements.Tam.massLev2 E r M

theorem supConst_nonneg2 (E : Type) [Field E] [NumberField E] (r d M : ℕ) (w : ℝ) : 0 ≤ supConst2 E r d M w := by
  unfold supConst2 locConst multBd
  have h2 : Even (2 * fdeg E * r ^ 2) := by rw [mul_assoc]; exact even_two_mul _
  refine mul_nonneg (mul_nonneg (div_nonneg (by positivity) (pow_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg _)) _))
    (h2.pow_nonneg _)) ?_
  unfold MainStatements.Tam.massLev2 MainStatements.Tam.massB
  positivity

section
open ReciprocityTheory.L2DbarEstimates GlobalTheory.SupConstSize Real

theorem supremum_constant_log_bound_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r d M : ℕ) (w L : ℝ), 2 ≤ r → 1 ≤ d → 1 ≤ M → 1 ≤ L → 1 ≤ w → Real.log (fdeg E * r) ≤ L → Real.log M ≤ 30 * L → Real.log (dE E) ≤ 4 * fdeg E * L → Real.log d ≤ 4 * L → Real.log w ≤ 2 * L → 1 ≤ supConst2 E r d M w ∧ Real.log (supConst2 E r d M w) ≤ 250 * (fdeg E : ℝ) ^ 2 * (r : ℝ) ^ 2 * L := by
  intro E _ _ _ r d M w L hr hd hM hL hw hfr hlM hdE hld hlw
  obtain ⟨hM1, hMl⟩ := size E r M L hr hM hL hfr hlM hdE
  exact locConst_mul_size E r d M w L (MainStatements.Tam.massLev2 E r M) hr hd hM hL hw hfr hlM hdE hld hlw hM1 hMl

end

end MainStatements.Tam.Plug

end
