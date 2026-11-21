module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterIntegralProperties
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_character_integral_properties : Ad3.R.G1a → Ad3.R.G1 := by
  exact @GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter.fundamental_domain_integral_central_vanishing
