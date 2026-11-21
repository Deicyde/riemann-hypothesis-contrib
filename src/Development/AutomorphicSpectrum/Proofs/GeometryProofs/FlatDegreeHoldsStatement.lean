module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatDegreeHolds
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.FlatDegree_holds : GlobalTheory.CompanionTheory.Ar.Fl.FlatDegree := by
  exact @GlobalTheory.CompanionTheory.Ar.Fl.flatDegree
