module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

@[expose] public section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.jacobi_maps_exist : MapsExist := by
  first | exact @GlobalTheory.CompanionTheory.JacobiMaps.mapsExist | exact GlobalTheory.CompanionTheory.JacobiMaps.mapsExist | (intros; apply GlobalTheory.CompanionTheory.JacobiMaps.mapsExist <;> assumption)
