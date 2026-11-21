module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformGenerationOfVanishing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_generation_of_vanishing : GradedNoeth → UniformVanishing → UniformGen := by
  exact @GlobalTheory.CompanionTheory.GE.uniformGen_of_gradedNoeth
