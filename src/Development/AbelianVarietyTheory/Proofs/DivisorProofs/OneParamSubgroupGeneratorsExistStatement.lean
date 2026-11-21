module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupGeneratorsExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneParamSubgroup_generators_exist : GlobalTheory.RealLift.GenEx := by
  exact @GlobalTheory.RealLiftGen.genEx
