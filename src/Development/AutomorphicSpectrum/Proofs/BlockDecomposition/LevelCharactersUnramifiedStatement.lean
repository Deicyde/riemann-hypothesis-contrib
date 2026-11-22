module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelCharactersUnramified
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps

@[expose] public section


theorem _root_.GlobalTheory.T.level_characters_unramified : PositivityTheory.SiegelWeilFormula.Gunr.LevChars := by
  first | exact @GlobalTheory.CompanionTheory.GunrLevChars.levChars | exact GlobalTheory.CompanionTheory.GunrLevChars.levChars | (intros; apply GlobalTheory.CompanionTheory.GunrLevChars.levChars <;> assumption)
