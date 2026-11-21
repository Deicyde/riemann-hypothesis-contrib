module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatakePowerNonvanishing
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan

@[expose] public section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_power_nonvanishing : PositivityTheory.SphericalProduct.SatPowNonvan := by
  exact @GlobalTheory.CompanionTheory.SatPow.satPowNonvan
