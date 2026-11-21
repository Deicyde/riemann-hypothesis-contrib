module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZetaMemPowInvPhiModuleLattice
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.AdmissibleSignatures

@[expose] public section

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_mem_pow_inv_phiModule_lattice : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.ZetaBound := by
  exact @GlobalTheory.ZetaDenominator.zetaBound
