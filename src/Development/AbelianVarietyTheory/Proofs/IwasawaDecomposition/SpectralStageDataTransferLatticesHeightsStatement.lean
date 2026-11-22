module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralStageDataTransferLatticesHeights
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage

@[expose] public section


theorem _root_.GlobalTheory.T.spectralStageData_transfer_lattices_heights : GlobalTheory.Mem.SRe.SxMv := by
  first | exact @GlobalTheory.Mem.SRe.SxPass.sxMv | exact GlobalTheory.Mem.SRe.SxPass.sxMv | (intros; apply GlobalTheory.Mem.SRe.SxPass.sxMv <;> assumption)
