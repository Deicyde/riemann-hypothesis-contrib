module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LemmaBTHolds
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NonemptyEquivOfCardHom

@[expose] public section


theorem _root_.GlobalTheory.T.LemmaBT_holds : GlobalTheory.CompanionTheory.Ar.BT.LemmaBT := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.lemmaBT_holds | exact GlobalTheory.CompanionTheory.Ar.BT.lemmaBT_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.lemmaBT_holds <;> assumption)
