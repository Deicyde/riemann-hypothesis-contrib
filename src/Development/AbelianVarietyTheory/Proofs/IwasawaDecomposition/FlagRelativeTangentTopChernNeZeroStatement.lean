module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernNeZero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

theorem _root_.GlobalTheory.T.flagRelativeTangentTopChern_ne_zero : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ), rootDiscr m ≠ 0 := by
  first | exact @GlobalTheory.GoodMetric.rootDiscr_ne_zero | exact GlobalTheory.GoodMetric.rootDiscr_ne_zero | (intros; apply GlobalTheory.GoodMetric.rootDiscr_ne_zero <;> assumption)
