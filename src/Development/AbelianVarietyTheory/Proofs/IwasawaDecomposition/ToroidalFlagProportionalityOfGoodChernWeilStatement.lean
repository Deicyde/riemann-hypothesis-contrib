module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalFlagProportionalityOfGoodChernWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidalFlagProportionality_of_goodChernWeil : GlobalTheory.Published.GoodChernWeil → GlobalTheory.Published.MumfordProportionality := by
  exact @GlobalTheory.Proportionality.mumfordProportionality_of_goodChernWeil
