module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenTheorem
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle

@[expose] public section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.tsen_theorem : GlobalTheory.NeedB.Tsen := by
  first | exact @GlobalTheory.NeedB.tsen | exact GlobalTheory.NeedB.tsen | (intros; apply GlobalTheory.NeedB.tsen <;> assumption)
