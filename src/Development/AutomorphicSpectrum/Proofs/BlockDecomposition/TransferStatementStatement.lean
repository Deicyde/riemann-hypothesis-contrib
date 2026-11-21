module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransferStatement
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transfer_statement : PositivityTheory.RgDs.K.Transfer := by
  exact @GlobalTheory.CompanionTheory.RgKeyTransfer.transfer
