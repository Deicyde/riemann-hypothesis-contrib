module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionFixed
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.Tail.PExp

theorem _root_.GlobalTheory.T.contraction_fixed : PositivityTheory.Rg.BcB.F.Tail.PExp.ContrFix := by
  first | exact @GlobalTheory.CompanionTheory.RepTensor.contrFix | exact GlobalTheory.CompanionTheory.RepTensor.contrFix | (intros; apply GlobalTheory.CompanionTheory.RepTensor.contrFix <;> assumption)
