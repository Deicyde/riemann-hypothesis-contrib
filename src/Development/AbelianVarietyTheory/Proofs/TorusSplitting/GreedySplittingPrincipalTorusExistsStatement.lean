module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.GreedySplittingPrincipalTorusExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound

@[expose] public section

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.GlobalTheory.T.greedy_splitting_principal_torus_exists : SplitStatement := by
  exact @GlobalTheory.greedy_splitting_exists
