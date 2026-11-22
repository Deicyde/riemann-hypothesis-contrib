module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPointOfSize
public import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumPt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtPtOfSize

@[expose] public section



section
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.weight_pt_of_size : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.WtPtAlt := by
  first | exact @_root_.GlobalTheory.RefSum.DivWt.wt_pt_of_cov_size | exact _root_.GlobalTheory.RefSum.DivWt.wt_pt_of_cov_size | (intros; apply _root_.GlobalTheory.RefSum.DivWt.wt_pt_of_cov_size <;> assumption)
end
