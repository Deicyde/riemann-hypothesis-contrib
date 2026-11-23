module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantFourierCoefficient
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

@[expose] public section

open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_constant_fourier_coefficient : MapsExist → PositivityTheory.PfSWUS.FourierZero → PcFc := by
  exact @GlobalTheory.CompanionTheory.PcFc.target
