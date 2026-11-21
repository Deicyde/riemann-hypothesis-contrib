module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleOrbitalFourierRankOneTransfer
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleOrbitalFourier_rankOne_transfer : RankOne := by
  exact @GlobalTheory.JR.RankOneTransfer.rankOne
