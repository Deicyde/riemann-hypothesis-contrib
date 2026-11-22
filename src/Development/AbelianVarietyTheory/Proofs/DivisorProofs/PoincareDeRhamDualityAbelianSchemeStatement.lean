module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareDeRhamDualityAbelianScheme
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality

@[expose] public section


theorem _root_.GlobalTheory.T.poincareDeRhamDuality_abelianScheme : GlobalTheory.Published.PoincareDeRhamDuality := by
  first | exact @GlobalTheory.poincareDeRhamDuality | exact GlobalTheory.poincareDeRhamDuality | (intros; apply GlobalTheory.poincareDeRhamDuality <;> assumption)
