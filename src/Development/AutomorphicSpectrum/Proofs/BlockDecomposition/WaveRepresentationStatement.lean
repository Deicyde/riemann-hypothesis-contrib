module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveRepresentation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

@[expose] public section


theorem _root_.GlobalTheory.T.wave_representation : GlobalTheory.CompanionTheory.KerFc.WaveRep := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.waveRep | exact GlobalTheory.CompanionTheory.KerFc.waveRep | (intros; apply GlobalTheory.CompanionTheory.KerFc.waveRep <;> assumption)
