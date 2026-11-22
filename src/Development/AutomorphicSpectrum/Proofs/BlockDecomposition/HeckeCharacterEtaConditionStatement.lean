module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterEtaCondition
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

@[expose] public section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.hecke_character_eta_condition : HeckeEta := by
  first | exact @GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta | exact GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta | (intros; apply GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta <;> assumption)
