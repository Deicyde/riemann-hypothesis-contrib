import BuildAid.Leniency.Open
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHarishChandraDiscreteSeries
import Formalism.SharpRestriction.Divisibility.SchurIrreducible -- for `export` of Formalism.BasicNotions.TH.DSRep, Formalism.BasicNotions.TH.GKMod (+2 more)
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_harishChandra_discreteSeries : ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T), ∃ M : UGKMod p q, M.M = D.HK := by
  first | exact @GlobalTheory.DiscreteSeriesUnitary.exists_unitary | exact GlobalTheory.DiscreteSeriesUnitary.exists_unitary | (intros; apply GlobalTheory.DiscreteSeriesUnitary.exists_unitary <;> assumption)
