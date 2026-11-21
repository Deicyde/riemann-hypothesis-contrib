module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveUniqueness
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wave_uniqueness : GlobalTheory.CompanionTheory.KerFc.WaveUniq := by
  exact @GlobalTheory.CompanionTheory.KerFc.waveUniq
