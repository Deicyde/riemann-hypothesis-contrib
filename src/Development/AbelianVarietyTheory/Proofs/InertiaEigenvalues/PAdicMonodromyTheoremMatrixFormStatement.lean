module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PAdicMonodromyTheoremMatrixForm
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pAdicMonodromyTheorem_matrixForm : MatThm := by
  exact @GlobalTheory.PMon.matThm_holds
