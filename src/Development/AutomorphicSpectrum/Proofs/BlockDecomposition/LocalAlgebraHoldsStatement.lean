module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig

@[expose] public section

open PositivityTheory.Rg.BcB.F.Eig
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_algebra_holds : LocAlg := by
  exact @GlobalTheory.CompanionTheory.LocHecke.locAlg
