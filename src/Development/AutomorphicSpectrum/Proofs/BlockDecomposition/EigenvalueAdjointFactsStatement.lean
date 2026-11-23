module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EigenvalueAdjointFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenvalue_adjoint_facts : GlobalTheory.CompanionTheory.KerFc.EvAdj := by
  exact @GlobalTheory.CompanionTheory.KerFc.evAdj
