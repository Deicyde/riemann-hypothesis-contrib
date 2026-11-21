module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MainProof
public import Formalism.UnipotentAdelicQuotients.WeylLatDual

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_lattice_duality : WeylLatticeDuality.Stmt := by
  exact @GlobalTheory.WeylLatDualProof.mainProof
