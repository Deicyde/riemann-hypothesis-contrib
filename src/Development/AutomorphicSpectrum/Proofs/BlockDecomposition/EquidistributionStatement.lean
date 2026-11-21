module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Equidistribution
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal

@[expose] public section

open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equidistribution : Equi := by
  exact @GlobalTheory.CompanionTheory.Equi.equi
