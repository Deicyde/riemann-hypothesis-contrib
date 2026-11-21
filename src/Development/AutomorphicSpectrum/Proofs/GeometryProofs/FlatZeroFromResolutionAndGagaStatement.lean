module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatZeroFromResolutionAndGaga
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_zero_from_resolution_and_gaga : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.CompanionTheory.Ar.Flat.GagaSections → GlobalTheory.CompanionTheory.Ar.Flat.FlatLineGenerator := by
  exact @GlobalTheory.CompanionTheory.Ar.Flat.A0.flat_zero_of_resolution_gaga
