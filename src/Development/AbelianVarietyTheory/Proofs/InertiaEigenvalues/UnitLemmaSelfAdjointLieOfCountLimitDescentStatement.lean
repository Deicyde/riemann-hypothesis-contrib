module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaSelfAdjointLieOfCountLimitDescent
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent

@[expose] public section

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLemmaSelfAdjointLie_of_count_limit_descent : CountIdentity → UnitaryLimit → LinearDescent → UnitLemmaLie := by
  exact @GlobalTheory.UnitLemma.LieEnd.unitLemmaLie_of
