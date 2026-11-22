module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeThirdProperty
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development

@[expose] public section


theorem _root_.GlobalTheory.T.hecke_third_property : PositivityTheory.Rg.Tf.Loc.H3 := by
  first | exact @GlobalTheory.CompanionTheory.TwistedCent.h3 | exact GlobalTheory.CompanionTheory.TwistedCent.h3 | (intros; apply GlobalTheory.CompanionTheory.TwistedCent.h3 <;> assumption)
