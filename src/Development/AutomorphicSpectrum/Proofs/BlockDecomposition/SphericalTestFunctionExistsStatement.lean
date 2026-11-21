module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalTestFunctionExists
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_test_function_exists : PositivityTheory.RgEis.TestSph := by
  exact @GlobalTheory.CompanionTheory.RgEisTestSph.testSph
