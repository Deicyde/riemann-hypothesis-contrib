module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrisPlusFrobEigenvectorRatioPadic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crisPlus_frob_eigenvector_ratio_padic : Ratio := by
  exact @GlobalTheory.PMon.ratio_holds
