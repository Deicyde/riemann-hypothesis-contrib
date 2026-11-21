module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmLocalDensitiesProductFormula
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDualIndex

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_localDensities_productFormula : GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.DensityProduct := by
  exact @GlobalTheory.Proof.cm_localDensities_productFormula.densityProduct
