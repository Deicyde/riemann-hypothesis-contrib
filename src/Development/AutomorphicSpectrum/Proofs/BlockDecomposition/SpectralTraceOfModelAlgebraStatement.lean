module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpectralTraceOfModelAlgebra
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig

@[expose] public section

open PositivityTheory.Rg.BcB.F.Eig

theorem _root_.GlobalTheory.T.spectral_trace_of_model_algebra : UModel → LocAlg → SpecTrace := by
  first | exact @GlobalTheory.CompanionTheory.SpecModel.specTrace | exact GlobalTheory.CompanionTheory.SpecModel.specTrace | (intros; apply GlobalTheory.CompanionTheory.SpecModel.specTrace <;> assumption)
