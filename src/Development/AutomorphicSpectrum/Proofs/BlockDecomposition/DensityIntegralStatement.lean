module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityIntegral
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut

@[expose] public section

noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.density_integral : PositivityTheory.PfSWUS.SchInf.DensInt := by
  first | exact @GlobalTheory.CompanionTheory.SW.DensInt.density_identity_inf | exact GlobalTheory.CompanionTheory.SW.DensInt.density_identity_inf | (intros; apply GlobalTheory.CompanionTheory.SW.DensInt.density_identity_inf <;> assumption)
