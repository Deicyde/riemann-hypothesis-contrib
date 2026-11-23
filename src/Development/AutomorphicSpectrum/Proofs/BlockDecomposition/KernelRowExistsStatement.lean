module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_row_exists : GlobalTheory.CompanionTheory.KerFc.FactorRapid → GlobalTheory.CompanionTheory.KerFc.EvAdj → GlobalTheory.CompanionTheory.KerFc.RowExists := by
  exact @GlobalTheory.CompanionTheory.KerFc.rowExists_of_factor
