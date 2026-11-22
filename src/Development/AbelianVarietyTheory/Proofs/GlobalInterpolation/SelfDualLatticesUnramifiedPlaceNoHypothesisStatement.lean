module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualLatticesUnramifiedPlaceNoHypothesis
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualLatticeActions

@[expose] public section


theorem _root_.GlobalTheory.T.selfDual_lattices_unramified_place_no_hypothesis : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.SelfDualLatticeLemmas := by
  first | exact @GlobalTheory.UnramSelfDualClosed.selfDualLatticeLemmas | exact GlobalTheory.UnramSelfDualClosed.selfDualLatticeLemmas | (intros; apply GlobalTheory.UnramSelfDualClosed.selfDualLatticeLemmas <;> assumption)
