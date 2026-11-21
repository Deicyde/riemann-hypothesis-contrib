module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisDataExists
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_data_exists : ∀ D : D7, galEx D := by
  exact @GlobalTheory.GalExist.galEx_all
