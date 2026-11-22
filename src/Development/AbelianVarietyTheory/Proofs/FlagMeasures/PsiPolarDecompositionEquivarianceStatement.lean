module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiPolarDecompositionEquivariance
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition

@[expose] public section

open GlobalTheory.Dec

theorem _root_.GlobalTheory.T.psi_polar_decomposition_equivariance : PsiPolar := by
  first | exact @GlobalTheory.Dec.psiPolar | exact GlobalTheory.Dec.psiPolar | (intros; apply GlobalTheory.Dec.psiPolar <;> assumption)
