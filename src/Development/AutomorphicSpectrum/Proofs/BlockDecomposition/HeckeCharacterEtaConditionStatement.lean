module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterEtaCondition
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

@[expose] public section

open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_character_eta_condition : HeckeEta := by
  exact @GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta
