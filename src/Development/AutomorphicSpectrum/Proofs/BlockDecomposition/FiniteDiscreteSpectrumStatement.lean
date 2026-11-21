module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDiscreteSpectrum
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.FinCut

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_discrete_spectrum : PositivityTheory.Rg.BcB.F.F5.FinDiscN := by
  exact @GlobalTheory.CompanionTheory.FinDiscN.finDiscN
