module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateSobolev
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

@[expose] public section


theorem _root_.GlobalTheory.T.left_translate_sobolev : GlobalTheory.CompanionTheory.KerFc.LtSob := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.ltSob | exact GlobalTheory.CompanionTheory.KerFc.ltSob | (intros; apply GlobalTheory.CompanionTheory.KerFc.ltSob <;> assumption)
