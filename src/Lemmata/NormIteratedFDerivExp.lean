module

public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

theorem Real.norm_iteratedFDeriv_exp (i : ℕ) (y : ℝ) : ‖iteratedFDeriv ℝ i Real.exp y‖ = Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := congrFun (iteratedDeriv_exp_const_mul i 1) y
  simp only [one_mul, one_pow] at h
  rw [show (fun s => Real.exp s) = Real.exp from rfl] at h
  rw [h, Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]
