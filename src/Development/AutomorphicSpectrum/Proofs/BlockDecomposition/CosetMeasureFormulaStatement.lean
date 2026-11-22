module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetMeasureFormula
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps

@[expose] public section


theorem _root_.GlobalTheory.T.coset_measure_formula : PositivityTheory.SiegelWeilFormula.Gunr.CosetMeas := by
  first | exact @GlobalTheory.CompanionTheory.GunrCoset.cosetMeas | exact GlobalTheory.CompanionTheory.GunrCoset.cosetMeas | (intros; apply GlobalTheory.CompanionTheory.GunrCoset.cosetMeas <;> assumption)
