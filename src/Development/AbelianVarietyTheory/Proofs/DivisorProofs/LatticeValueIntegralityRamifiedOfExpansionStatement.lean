module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIntegralityRamifiedOfExpansion
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeValueIntegrality_ramified_of_expansion : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement → Expansion → LatIntRam := by
  exact @GlobalTheory.LatValRam.latIntRam
