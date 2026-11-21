module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroFrobVectorResidueZero
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_frobVector_residue_zero : ExII := by
  exact @GlobalTheory.PMonII.exII
