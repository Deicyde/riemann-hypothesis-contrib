module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoBasesComparison
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic

@[expose] public section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_bases_comparison : TwoBases := by
  exact @GlobalTheory.CompanionTheory.LinAlg.twoBases
