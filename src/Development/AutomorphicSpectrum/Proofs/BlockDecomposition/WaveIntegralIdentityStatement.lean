module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveIntegralIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

@[expose] public section


theorem _root_.GlobalTheory.T.wave_integral_identity : GlobalTheory.CompanionTheory.KerFc.WaveInt := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.waveInt | exact GlobalTheory.CompanionTheory.KerFc.waveInt | (intros; apply GlobalTheory.CompanionTheory.KerFc.waveInt <;> assumption)
