module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityInert
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_inert : PositivityTheory.Rg.BcB.F.MLM.MuInert := by
  exact @GlobalTheory.CompanionTheory.MuInertPlace.muInert
