module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableCoshPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

theorem _root_.GlobalTheory.T.measurable_coshPow' : ∀ (p q : ℕ) (c : ℝ), Measurable (coshPow c : UpqT p q → ℝ) := by
  first | exact @GlobalTheory.CoshPowMeas.measurable_coshPow | exact GlobalTheory.CoshPowMeas.measurable_coshPow | (intros; apply GlobalTheory.CoshPowMeas.measurable_coshPow <;> assumption)
