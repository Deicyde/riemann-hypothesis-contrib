module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTotalOfHeckeEta
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

@[expose] public section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.theta_total_of_hecke_eta : HeckeEta → ThTotal := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.thTotal | exact GlobalTheory.CompanionTheory.ThTot.thTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.thTotal <;> assumption)
