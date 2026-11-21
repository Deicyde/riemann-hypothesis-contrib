module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HerbrandQuotientEigenDet
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.herbrandQuotient_eigen_det : GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.HerbrandDet := by
  exact @GlobalTheory.HerbrandAlg.herbrandDet
