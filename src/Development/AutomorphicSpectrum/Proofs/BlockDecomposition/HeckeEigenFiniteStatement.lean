module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeEigenFinite
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.Tail.PExp

theorem _root_.GlobalTheory.T.hecke_eigen_finite : PositivityTheory.Rg.BcB.F.Tail.PExp.HkEFin := by
  first | exact @GlobalTheory.CompanionTheory.HeckeEnd.hkE_fin | exact GlobalTheory.CompanionTheory.HeckeEnd.hkE_fin | (intros; apply GlobalTheory.CompanionTheory.HeckeEnd.hkE_fin <;> assumption)
