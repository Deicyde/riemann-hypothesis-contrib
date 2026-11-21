module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupHaarPropertiesProof
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicUnitaryGroupHaarProperties_proof : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.AdelicUnitaryHaar := by
  exact @GlobalTheory.adelicUnitaryHaar_holds
