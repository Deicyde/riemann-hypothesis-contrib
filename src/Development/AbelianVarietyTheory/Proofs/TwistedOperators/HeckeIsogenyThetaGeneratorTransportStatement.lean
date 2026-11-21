module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyThetaGeneratorTransport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLawsOfTransport

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeIsogeny_thetaGenerator_transport : GlobalTheory.HeckePointLaw.ThetaTransportLaw := by
  exact @GlobalTheory.ThetaTransport.thetaTransportLaw
