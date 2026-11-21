import BuildAid.Leniency.Open
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.IsCond
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OverOnePrimeOfCardLeOne -- for `export` of Formalism.L2.Col.Fields.IsCond

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.Mem

theorem Base.fields_isCond : ∀ (B : Base) (X : PreX B.toPre), B.fields.IsCond (B.primes X).cond := by
  intro B X j
  exact UpperTheory.Ram.isCond_condN B.host j

end GlobalTheory.Mem
