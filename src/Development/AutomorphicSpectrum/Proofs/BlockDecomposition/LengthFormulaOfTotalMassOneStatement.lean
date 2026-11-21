module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFormulaOfTotalMassOne
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide

@[expose] public section

open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_formula_of_total_mass_one : PositivityTheory.SiegelWeilFormula.Densx.MassOne → Prop1 := by
  exact @GlobalTheory.CompanionTheory.Mass.Rank.mass_formula_of_total_mass_one
