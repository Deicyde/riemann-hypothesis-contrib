module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceStrip
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

@[expose] public section

open GlobalTheory.CompanionTheory.EGlue

theorem _root_.GlobalTheory.T.convergence_strip : GlobalTheory.CompanionTheory.EGlue.ConvStrip := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.ConvStripProof.convStrip | exact GlobalTheory.CompanionTheory.EGlue.ConvStripProof.convStrip | (intros; apply GlobalTheory.CompanionTheory.EGlue.ConvStripProof.convStrip <;> assumption)
