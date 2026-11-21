module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAct

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitEx_every_datum : ∀ D : D7, Formalism.L2.SplitEx D := by
  exact @GlobalTheory.SplitConjPlace.splitEx_all
