module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainStepVectorsAndAdjointVectorsAreTheta
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.StepVecThetaLem

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainStepVectors_and_adjointVectors_areTheta : ∀ D : D7, Formalism.IndefR.Fin.VecThetaSD D := by
  exact @GlobalTheory.VecTheta.vecThetaSD
