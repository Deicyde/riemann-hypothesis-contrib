module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantHolds
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor

@[expose] public section


theorem _root_.GlobalTheory.T.finite_constant_holds : GlobalTheory.CompanionTheory.Ar.Flat.FinConst := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.finConst_of_all_hosts | exact GlobalTheory.CompanionTheory.Ar.Flat.finConst_of_all_hosts | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.finConst_of_all_hosts <;> assumption)
