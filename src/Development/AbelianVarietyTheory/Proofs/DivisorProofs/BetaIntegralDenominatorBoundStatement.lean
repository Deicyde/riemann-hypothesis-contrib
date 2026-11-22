module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaIntegralDenominatorBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

@[expose] public section

open GlobalTheory.LeviCut

theorem _root_.GlobalTheory.T.beta_integral_denominator_bound : GlobalTheory.LeviCut.BetaDen := by
  first | exact @GlobalTheory.LeviCut.betaDen | exact GlobalTheory.LeviCut.betaDen | (intros; apply GlobalTheory.LeviCut.betaDen <;> assumption)
