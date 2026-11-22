module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EigenvalueAdjointFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

@[expose] public section


theorem _root_.GlobalTheory.T.eigenvalue_adjoint_facts : GlobalTheory.CompanionTheory.KerFc.EvAdj := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.evAdj | exact GlobalTheory.CompanionTheory.KerFc.evAdj | (intros; apply GlobalTheory.CompanionTheory.KerFc.evAdj <;> assumption)
