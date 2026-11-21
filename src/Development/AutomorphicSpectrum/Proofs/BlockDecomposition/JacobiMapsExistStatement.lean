module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

@[expose] public section

open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobi_maps_exist : MapsExist := by
  exact @GlobalTheory.CompanionTheory.JacobiMaps.mapsExist
