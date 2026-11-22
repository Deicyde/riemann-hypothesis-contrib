module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveUniqueness
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

@[expose] public section


theorem _root_.GlobalTheory.T.wave_uniqueness : GlobalTheory.CompanionTheory.KerFc.WaveUniq := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.waveUniq | exact GlobalTheory.CompanionTheory.KerFc.waveUniq | (intros; apply GlobalTheory.CompanionTheory.KerFc.waveUniq <;> assumption)
