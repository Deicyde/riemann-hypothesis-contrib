module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatDegreeHolds
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree

@[expose] public section


theorem _root_.GlobalTheory.T.FlatDegree_holds : GlobalTheory.CompanionTheory.Ar.Fl.FlatDegree := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.flatDegree | exact GlobalTheory.CompanionTheory.Ar.Fl.flatDegree | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.flatDegree <;> assumption)
