module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphisms
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalAlgebraisation_morphisms' : GlobalTheory.Published.FormalAlgebraisation.Morphisms := by
  exact @GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms
