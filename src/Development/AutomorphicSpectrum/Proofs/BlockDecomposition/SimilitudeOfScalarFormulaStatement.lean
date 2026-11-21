module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeOfScalarFormula
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide

@[expose] public section

open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitude_of_scalar_formula : Scal → Simil := by
  exact @GlobalTheory.CompanionTheory.SW.BaseSimil.simil
