module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeWeylInvariant
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySatake_weylInvariant : Formalism.UG.SatWeyl := by
  exact @GlobalTheory.SatakeWeyl.satWeyl
