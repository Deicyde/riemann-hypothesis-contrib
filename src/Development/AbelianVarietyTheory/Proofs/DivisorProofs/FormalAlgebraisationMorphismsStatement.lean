module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphisms
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation

@[expose] public section


theorem _root_.GlobalTheory.T.formalAlgebraisation_morphisms' : GlobalTheory.Published.FormalAlgebraisation.Morphisms := by
  first | exact @GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms | exact GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms | (intros; apply GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms <;> assumption)
