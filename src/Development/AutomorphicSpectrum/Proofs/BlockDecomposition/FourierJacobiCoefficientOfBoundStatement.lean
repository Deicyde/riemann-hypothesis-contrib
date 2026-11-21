module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiCoefficientOfBound
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

@[expose] public section

open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_jacobi_coefficient_of_bound : PcBound → CfFJ := by
  exact @GlobalTheory.CompanionTheory.CfFJ.cfFJ_of_pcBound
