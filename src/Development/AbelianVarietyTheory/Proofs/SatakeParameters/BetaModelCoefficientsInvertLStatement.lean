module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BetaModelCoefficientsInvertL
public import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob

@[expose] public section


theorem _root_.GlobalTheory.T.beta_model_coefficients_invert_l : Formalism.L2.KerInert.BeCob.BeCoef := by
  first | exact @GlobalTheory.BeCoefficients.beCoef | exact GlobalTheory.BeCoefficients.beCoef | (intros; apply GlobalTheory.BeCoefficients.beCoef <;> assumption)
