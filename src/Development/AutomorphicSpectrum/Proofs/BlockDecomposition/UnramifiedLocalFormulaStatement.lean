module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedLocalFormula
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs

@[expose] public section

open Filter Topology

theorem _root_.GlobalTheory.T.unramified_local_formula : PositivityTheory.PfSWUS.Loc.UnrFormula := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.unrFormula | exact GlobalTheory.CompanionTheory.UnrDens.unrFormula | (intros; apply GlobalTheory.CompanionTheory.UnrDens.unrFormula <;> assumption)
