module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.cartanEigen_orthonormalFrame_exists : GlobalTheory.RealLift.FrameEx := by
  first | exact @GlobalTheory.RealLift.frameEx_holds | exact GlobalTheory.RealLift.frameEx_holds | (intros; apply GlobalTheory.RealLift.frameEx_holds <;> assumption)
