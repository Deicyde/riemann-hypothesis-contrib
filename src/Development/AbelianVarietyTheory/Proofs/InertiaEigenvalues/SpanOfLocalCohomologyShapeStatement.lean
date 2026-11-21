module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanOfLocalCohomologyShape
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_of_local_cohomology_shape : ReciprocityTheory.ChartRestriction.T2.JSpan := by
  exact @GlobalTheory.jSpan_holds
