module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityLevelFormula
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_level_formula : PositivityTheory.SiegelWeilFormula.Gunr.NuLev := by
  exact @GlobalTheory.CompanionTheory.SiegLoc.NuIndex.nuLev
