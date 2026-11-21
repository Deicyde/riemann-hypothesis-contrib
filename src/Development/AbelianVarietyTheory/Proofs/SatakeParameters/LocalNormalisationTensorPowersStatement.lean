module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationTensorPowers
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementNorm

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localNormalisation_tensorPowers : Formalism.L2.AlgTh.LocNormPow := by
  exact @GlobalTheory.locNormPow_tensorPowers
