module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedLocalFormula
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs

@[expose] public section

open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_local_formula : PositivityTheory.PfSWUS.Loc.UnrFormula := by
  exact @GlobalTheory.CompanionTheory.UnrDens.unrFormula
