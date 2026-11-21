module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDetectedSubgroupTowerRatProof
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noDetectedSubgroupTowerRat_proof : NoTowerQ := by
  exact @GlobalTheory.PMon.Ram.noTowerQ_holds
