import BuildAid.Leniency.Open
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
import Formalism.SharpRestriction.Divisibility.SchurIrreducible -- for `export` of Formalism.BasicNotions.TH.GrpData

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.DetSqrtCover

theorem nonempty_grpData : ∀ p q : ℕ, Nonempty (GrpData p q) :=
  fun p q => ⟨grpOf p q MeasureTheory.Measure.haar⟩

end GlobalTheory.DetSqrtCover
