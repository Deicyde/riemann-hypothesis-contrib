module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogPeriodChowlaSelberg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta

@[expose] public section


theorem _root_.GlobalTheory.T.meanLogPeriod_chowlaSelberg : GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod := by
  first | exact @GlobalTheory.MeanPeriodClosed.meanPeriod | exact GlobalTheory.MeanPeriodClosed.meanPeriod | (intros; apply GlobalTheory.MeanPeriodClosed.meanPeriod <;> assumption)
