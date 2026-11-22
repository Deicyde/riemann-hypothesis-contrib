module

public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.FinalP
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.WeylInt
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.ZpClosedToAddSubgroup
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.CompEqZeroOfNotDle

@[expose] public section

namespace Formalism.InvariantFactorPaths.PW.Top

theorem weylInt : WeylInt := weyl_integral_holds
theorem weylP : WeylP := weylP_of weylInt lattice_basis_polynomial

private theorem intP_statement : IntP := by
  exact intP_of (typeInt_of invariant_natural_holds (homInv_of invariant_inverse_holds) (schurTrace_of invariant_inverse_holds)) lattice_basis_polynomial

theorem extP : ExtP := extP_of intP_statement
theorem dischargeW : DischargeW := dischargeW_of weylP
theorem dischargeE : DischargeE := dischargeE_of extP

end Formalism.InvariantFactorPaths.PW.Top
