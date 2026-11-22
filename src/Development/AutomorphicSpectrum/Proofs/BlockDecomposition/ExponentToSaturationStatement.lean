module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentToSaturation
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ExpToSat

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.Tail.PExp

theorem _root_.GlobalTheory.T.exponent_to_saturation : PositivityTheory.Rg.BcB.F.Tail.PExp.ExpToSat := by
  first | exact @GlobalTheory.CompanionTheory.ExpProd.expToSat | exact GlobalTheory.CompanionTheory.ExpProd.expToSat | (intros; apply GlobalTheory.CompanionTheory.ExpProd.expToSat <;> assumption)
