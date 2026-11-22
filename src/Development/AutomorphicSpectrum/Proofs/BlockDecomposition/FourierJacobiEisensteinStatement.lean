module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiEisenstein
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

@[expose] public section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.fourier_jacobi_eisenstein : ZUnfold → ThTwist → FJEis := by
  first | exact @GlobalTheory.CompanionTheory.FJE.fjEis | exact GlobalTheory.CompanionTheory.FJE.fjEis | (intros; apply GlobalTheory.CompanionTheory.FJE.fjEis <;> assumption)
