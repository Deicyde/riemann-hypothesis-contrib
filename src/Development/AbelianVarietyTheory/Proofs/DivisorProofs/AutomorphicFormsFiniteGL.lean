module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL

@[expose] public section

namespace GlobalTheory

theorem automorphicFormsFiniteGL : GlobalTheory.Published.AutomorphicFormsFiniteGL :=
  UpperTheory.V.Af.formsFiniteGL

end GlobalTheory
