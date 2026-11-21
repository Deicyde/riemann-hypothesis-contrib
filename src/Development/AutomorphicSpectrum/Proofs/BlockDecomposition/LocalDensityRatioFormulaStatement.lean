module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityRatioFormula
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide

@[expose] public section

open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_density_ratio_formula : Ratio := by
  exact @GlobalTheory.CompanionTheory.RatioBase.ratio
