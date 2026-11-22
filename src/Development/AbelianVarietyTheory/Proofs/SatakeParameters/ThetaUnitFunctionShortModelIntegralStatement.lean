module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaUnitFunctionShortModelIntegral
public import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob

@[expose] public section


theorem _root_.GlobalTheory.T.thetaUnitFunction_shortModel_integral : Formalism.L2.KerInert.BeCob.ThetaTie := by
  first | exact @GlobalTheory.ShortModelTheta.thetaTie_holds | exact GlobalTheory.ShortModelTheta.thetaTie_holds | (intros; apply GlobalTheory.ShortModelTheta.thetaTie_holds <;> assumption)
