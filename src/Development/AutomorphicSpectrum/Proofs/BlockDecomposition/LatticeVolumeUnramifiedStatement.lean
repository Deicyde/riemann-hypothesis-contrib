module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeVolumeUnramified
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_volume_unramified : PositivityTheory.SiegelWeilFormula.Gunr.VolLat := by
  exact @GlobalTheory.CompanionTheory.GunrVol.volLat
