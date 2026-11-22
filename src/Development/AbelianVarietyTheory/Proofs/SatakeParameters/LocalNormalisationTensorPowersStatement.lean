module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationTensorPowers
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementNorm

@[expose] public section


theorem _root_.GlobalTheory.T.localNormalisation_tensorPowers : Formalism.L2.AlgTh.LocNormPow := by
  first | exact @GlobalTheory.locNormPow_tensorPowers | exact GlobalTheory.locNormPow_tensorPowers | (intros; apply GlobalTheory.locNormPow_tensorPowers <;> assumption)
