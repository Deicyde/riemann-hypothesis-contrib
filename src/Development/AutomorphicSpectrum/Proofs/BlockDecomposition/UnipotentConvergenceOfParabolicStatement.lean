module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentConvergenceOfParabolic
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_convergence_of_parabolic : PositivityTheory.RgEis.ParLaw → PositivityTheory.RgEis.ConvU := by
  exact @GlobalTheory.CompanionTheory.RgEis.UnitaryConv.convU_of_parLaw
