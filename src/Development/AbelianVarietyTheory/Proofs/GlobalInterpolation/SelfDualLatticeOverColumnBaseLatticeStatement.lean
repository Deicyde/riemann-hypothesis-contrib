module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualLatticeOverColumnBaseLattice
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SplittingProjection

@[expose] public section


theorem _root_.GlobalTheory.T.selfDualLattice_over_columnBaseLattice : GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.SelfDualOverBase := by
  first | exact @GlobalTheory.OverObj.selfDualOverBase | exact GlobalTheory.OverObj.selfDualOverBase | (intros; apply GlobalTheory.OverObj.selfDualOverBase <;> assumption)
