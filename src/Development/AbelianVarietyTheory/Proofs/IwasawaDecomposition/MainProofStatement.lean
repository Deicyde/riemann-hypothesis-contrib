module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MainProof
public import Formalism.UnipotentAdelicQuotients.WeylLatDual

@[expose] public section


theorem _root_.GlobalTheory.T.weyl_lattice_duality : WeylLatticeDuality.Stmt := by
  first | exact @GlobalTheory.WeylLatDualProof.mainProof | exact GlobalTheory.WeylLatDualProof.mainProof | (intros; apply GlobalTheory.WeylLatDualProof.mainProof <;> assumption)
