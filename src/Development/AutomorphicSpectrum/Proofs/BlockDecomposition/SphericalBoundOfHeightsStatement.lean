module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalBoundOfHeights
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

@[expose] public section

open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_bound_of_heights : HtExist → SphBound := by
  exact @GlobalTheory.CompanionTheory.SphPole.sphBound_of_htExist
