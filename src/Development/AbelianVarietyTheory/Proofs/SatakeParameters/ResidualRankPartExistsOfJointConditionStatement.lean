module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidualRankPartExistsOfJointCondition
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residualRankPartExists_of_jointCondition : ∀ D : D7, GlobalDatumResidualRepCondition D → RbEx D := by
  exact @GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho
