module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCountTail
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.Tail.PExp

theorem _root_.GlobalTheory.T.coset_count_tail : PositivityTheory.Rg.BcB.F.Tail.PExp.CosetCount := by
  first | exact @GlobalTheory.CompanionTheory.IwahoriCount.cosetCount | exact GlobalTheory.CompanionTheory.IwahoriCount.cosetCount | (intros; apply GlobalTheory.CompanionTheory.IwahoriCount.cosetCount <;> assumption)
