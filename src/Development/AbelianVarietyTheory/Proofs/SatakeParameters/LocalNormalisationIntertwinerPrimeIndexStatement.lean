module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationIntertwinerPrimeIndex
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementNorm

@[expose] public section


theorem _root_.GlobalTheory.T.localNormalisation_intertwiner_prime_index : Formalism.L2.AlgTh.LocNormInter := by
  first | exact @GlobalTheory.locNormInter | exact GlobalTheory.locNormInter | (intros; apply GlobalTheory.locNormInter <;> assumption)
