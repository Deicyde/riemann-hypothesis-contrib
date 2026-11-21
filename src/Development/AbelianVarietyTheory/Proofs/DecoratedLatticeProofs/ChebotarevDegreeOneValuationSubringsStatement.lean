module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChebotarevDegreeOneValuationSubrings
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModChebOm

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chebotarev_degreeOne_valuationSubrings : ReciprocityTheory.ChartRestriction.L1.ChebOmSt := by
  exact @GlobalTheory.chebOmSt_holds
