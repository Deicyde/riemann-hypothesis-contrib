import BuildAid.Leniency.Open
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveRankEmbedding
import Formalism.SharpRestriction.Divisibility.SchurIrreducible -- for `export` of Formalism.BasicNotions.TH.Ix, Formalism.BasicNotions.TH.Pol
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_rank_embedding : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ), Function.Injective (embR P Q R h k) := by
  first | exact @GlobalTheory.CharPair.embR_injective | exact GlobalTheory.CharPair.embR_injective | (intros; apply GlobalTheory.CharPair.embR_injective <;> assumption)
