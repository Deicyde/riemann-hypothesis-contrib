module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidueCountOfSsRank
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeCharEqOfLAdicRealisation
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ResidualCount

@[expose] public section



section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.resCount_of_valRing_ssList_ssRank : ValRingModel → SSList → SSRankUnique → _root_.GlobalTheory.StringRepresentationDecomposition.ResidueCount := by
  first | exact @_root_.GlobalTheory.ResidualRankCount.residual_count_alt_alt | exact _root_.GlobalTheory.ResidualRankCount.residual_count_alt_alt | (intros; apply _root_.GlobalTheory.ResidualRankCount.residual_count_alt_alt <;> assumption)
end
