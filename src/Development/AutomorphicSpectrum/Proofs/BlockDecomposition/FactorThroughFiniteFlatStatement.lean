module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorThroughFiniteFlat
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite

@[expose] public section


theorem _root_.GlobalTheory.T.factor_through_finite_flat : PositivityTheory.Tls2.Zar3.Ch1.FactorThroughFF := by
  first | exact @GlobalTheory.CompanionTheory.FlatFactor.factorThroughFF | exact GlobalTheory.CompanionTheory.FlatFactor.factorThroughFF | (intros; apply GlobalTheory.CompanionTheory.FlatFactor.factorThroughFF <;> assumption)
