module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoostDecompositionNormBoundOfEmbeddingLaws
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists

@[expose] public section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boostDecompositionNormBound_of_embeddingLaws : EmbLaws → Boost := by
  exact @GlobalTheory.SepReal.boost_of_embLaws
