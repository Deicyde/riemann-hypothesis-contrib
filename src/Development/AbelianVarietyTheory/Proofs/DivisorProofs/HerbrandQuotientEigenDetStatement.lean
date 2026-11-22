module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HerbrandQuotientEigenDet
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity

@[expose] public section


theorem _root_.GlobalTheory.T.herbrandQuotient_eigen_det : GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.HerbrandDet := by
  first | exact @GlobalTheory.HerbrandAlg.herbrandDet | exact GlobalTheory.HerbrandAlg.herbrandDet | (intros; apply GlobalTheory.HerbrandAlg.herbrandDet <;> assumption)
