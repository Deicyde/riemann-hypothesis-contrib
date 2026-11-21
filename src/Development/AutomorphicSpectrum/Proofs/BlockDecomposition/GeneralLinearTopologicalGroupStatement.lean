module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearTopologicalGroup
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.general_linear_topological_group : PositivityTheory.RgEis.GrpTop := by
  exact @GlobalTheory.CompanionTheory.RgEisTop.grpTop
