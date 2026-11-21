module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveRepresentation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wave_representation : GlobalTheory.CompanionTheory.KerFc.WaveRep := by
  exact @GlobalTheory.CompanionTheory.KerFc.waveRep
