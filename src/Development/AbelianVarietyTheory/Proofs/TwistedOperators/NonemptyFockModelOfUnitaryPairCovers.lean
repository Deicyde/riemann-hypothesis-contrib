import BuildAid.Leniency.Open
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyFockModelUnitaryDualPairStatement
import Formalism.SharpRestriction.Divisibility.SchurIrreducible -- for `export` of Formalism.BasicNotions.TH.FockData, Formalism.BasicNotions.TH.GrpData

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory

theorem nonempty_fockData_of_covers :
    ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q)
      (T2 : GrpData r s), Nonempty (FockData T0 T1 T2) :=
  GlobalTheory.T.nonempty_fockModel_unitary_dual_pair

end GlobalTheory
