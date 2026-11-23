module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCoordinates
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut

@[expose] public section

noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_coordinates : PositivityTheory.PfSWUS.SchInf.CoordInf := by
  exact @GlobalTheory.CompanionTheory.SW.CoordR.coordInf
