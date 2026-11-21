module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorHecke
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_hecke : PositivityTheory.Rg.BcB.F.Tail.PExp.TensHk := by
  exact @GlobalTheory.CompanionTheory.TensHkSum.tensHk
