module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitTwistBound
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.BlockTypes

@[expose] public section

open scoped Classical
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_twist_bound : PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5.TwBound := by
  exact @GlobalTheory.CompanionTheory.TotalTrace.twBound
