module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralLocalDualityOfLocalTateDuality
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section


theorem _root_.GlobalTheory.T.integral_localDuality_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ReciprocityTheory.ChartRestriction.T2.IntIso := by
  first | exact @GlobalTheory.LocDualInt.int_iso_of_localTateDuality | exact GlobalTheory.LocDualInt.int_iso_of_localTateDuality | (intros; apply GlobalTheory.LocDualInt.int_iso_of_localTateDuality <;> assumption)
