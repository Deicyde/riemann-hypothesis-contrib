module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabSelfDualLatticeTransitiveOnLength
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabSelfDualLattice_transitive_on_length : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive := by
  exact @GlobalTheory.StabOrbit.stabTransitive
