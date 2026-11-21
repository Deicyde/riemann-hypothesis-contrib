module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiHolomorphicNearPositiveMatricesAtOne
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition

@[expose] public section

open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_holomorphic_near_positive_matrices_at_one : PsBasic := by
  exact @GlobalTheory.Dec.psBasic
