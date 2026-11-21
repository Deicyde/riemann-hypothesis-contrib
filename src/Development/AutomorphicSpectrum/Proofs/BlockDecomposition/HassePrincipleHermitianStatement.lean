module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrincipleHermitian
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide

@[expose] public section

open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasse_principle_hermitian : Hasse := by
  exact @GlobalTheory.CompanionTheory.SW.BaseHasse.hasse
