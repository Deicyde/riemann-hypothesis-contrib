module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyScalarIsUnitOnIntegralModels
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeyScalar_isUnit_on_integralModels : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.KeyUnitOnModels := by
  exact @GlobalTheory.KeyUnitModels.keyUnitOnModels
