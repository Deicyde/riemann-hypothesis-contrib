module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyThetaGeneratorTransport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLawsOfTransport

@[expose] public section


theorem _root_.GlobalTheory.T.heckeIsogeny_thetaGenerator_transport : GlobalTheory.HeckePointLaw.ThetaTransportLaw := by
  first | exact @GlobalTheory.ThetaTransport.thetaTransportLaw | exact GlobalTheory.ThetaTransport.thetaTransportLaw | (intros; apply GlobalTheory.ThetaTransport.thetaTransportLaw <;> assumption)
