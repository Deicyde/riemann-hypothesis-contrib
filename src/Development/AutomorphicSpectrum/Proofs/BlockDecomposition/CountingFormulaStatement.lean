module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountingFormula
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal

@[expose] public section

open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.counting_formula : TestEx → LSide → RSide → Cnt := by
  exact @GlobalTheory.CompanionTheory.RgMass.cnt
