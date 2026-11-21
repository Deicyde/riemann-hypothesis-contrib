module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityFormula
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide

@[expose] public section

open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_density_formula : Dens := by
  exact @GlobalTheory.CompanionTheory.SW.RankOne.dens
