module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantReductionReal
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.LeviCommutantWordReduction

@[expose] public section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutant_reduction_real : PositivityTheory.RgBcC.RealD.LeviCommutantWordReduction := by
  exact @GlobalTheory.CompanionTheory.BlockCapelliWords.commutant_block_capelli_words
