module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

@[expose] public section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.partial_constant_term_bound : PcBound := by
  first | exact @GlobalTheory.CompanionTheory.PcB.pcBound | exact GlobalTheory.CompanionTheory.PcB.pcBound | (intros; apply GlobalTheory.CompanionTheory.PcB.pcBound <;> assumption)
