module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMatrixIntegral
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.BasisSet

@[expose] public section


theorem _root_.GlobalTheory.T.local_matrix_integral : PositivityTheory.SiegelWeilFormula.Gunr.LocMat := by
  first | exact @GlobalTheory.CompanionTheory.Gunr.locMat | exact GlobalTheory.CompanionTheory.Gunr.locMat | (intros; apply GlobalTheory.CompanionTheory.Gunr.locMat <;> assumption)
