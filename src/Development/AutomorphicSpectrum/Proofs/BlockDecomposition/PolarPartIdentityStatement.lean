module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentity
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

@[expose] public section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.polar_part_identity : MapsExist → HtExist → HeckeEta → RightId → PoleReal → FJEis → PcBound → RSec → EisHol → ThTotal → CfFJ → PcFc → SphBound → Polar := by
  first | exact @GlobalTheory.CompanionTheory.RswPolar.polar | exact GlobalTheory.CompanionTheory.RswPolar.polar | (intros; apply GlobalTheory.CompanionTheory.RswPolar.polar <;> assumption)
