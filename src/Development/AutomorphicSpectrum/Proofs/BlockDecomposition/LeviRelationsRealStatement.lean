module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRelationsReal
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.LeviCommutantWordReduction

@[expose] public section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_relations_real : PositivityTheory.RgBcC.RealD.LevRel := by
  exact @GlobalTheory.CompanionTheory.LevChainRel.levRel
