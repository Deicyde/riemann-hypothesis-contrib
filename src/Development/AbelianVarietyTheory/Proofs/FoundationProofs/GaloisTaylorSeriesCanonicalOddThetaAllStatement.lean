module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisTaylorSeriesCanonicalOddThetaAll
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_taylorSeries_canonicalOddTheta_all : ∀ D : D7, galSg D := by
  exact @GlobalTheory.SigmaConj.galSg_all
