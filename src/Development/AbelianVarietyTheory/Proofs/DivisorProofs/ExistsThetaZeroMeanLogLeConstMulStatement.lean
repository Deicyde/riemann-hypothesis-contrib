module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaZeroMeanLogLeConstMul
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans

@[expose] public section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.exists_thetaZeroMeanLogLeConstMul : ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.MeanLeC C D := by
  first | exact @GlobalTheory.Theta0MeanLeC.theta0MeanLeC | exact GlobalTheory.Theta0MeanLeC.theta0MeanLeC | (intros; apply GlobalTheory.Theta0MeanLeC.theta0MeanLeC <;> assumption)
