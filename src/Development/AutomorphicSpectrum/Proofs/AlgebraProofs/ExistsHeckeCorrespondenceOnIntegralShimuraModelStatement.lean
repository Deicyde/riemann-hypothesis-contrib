module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHeckeCorrespondenceOnIntegralShimuraModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagClosure

@[expose] public section


theorem _root_.GlobalTheory.T.exists_heckeCorrespondence_on_integral_shimuraModel : GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureCut.Statement := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.SegreFlag.segreFlagClosureCut | exact GlobalTheory.CompanionTheory.CommAlg.SegreFlag.segreFlagClosureCut | (intros; apply GlobalTheory.CompanionTheory.CommAlg.SegreFlag.segreFlagClosureCut <;> assumption)
