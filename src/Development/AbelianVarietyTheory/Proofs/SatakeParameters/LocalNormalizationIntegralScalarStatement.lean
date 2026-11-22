module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalizationIntegralScalar
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementNorm

@[expose] public section


theorem _root_.GlobalTheory.T.localNormalization_integral_scalar : Formalism.L2.AlgTh.LocNormScale := by
  first | exact @GlobalTheory.locNormScale | exact GlobalTheory.locNormScale | (intros; apply GlobalTheory.locNormScale <;> assumption)
