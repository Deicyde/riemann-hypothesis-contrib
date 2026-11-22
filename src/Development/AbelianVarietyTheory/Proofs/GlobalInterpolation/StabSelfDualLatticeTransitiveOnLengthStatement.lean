module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabSelfDualLatticeTransitiveOnLength
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices

@[expose] public section


theorem _root_.GlobalTheory.T.stabSelfDualLattice_transitive_on_length : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive := by
  first | exact @GlobalTheory.StabOrbit.stabTransitive | exact GlobalTheory.StabOrbit.stabTransitive | (intros; apply GlobalTheory.StabOrbit.stabTransitive <;> assumption)
