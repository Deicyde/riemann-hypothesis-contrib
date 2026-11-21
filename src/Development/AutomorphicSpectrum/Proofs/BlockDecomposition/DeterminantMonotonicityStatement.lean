module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeterminantMonotonicity
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub

@[expose] public section

open Matrix PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_monotonicity : DetMono := by
  exact @GlobalTheory.CompanionTheory.DetMonotone.detMono
