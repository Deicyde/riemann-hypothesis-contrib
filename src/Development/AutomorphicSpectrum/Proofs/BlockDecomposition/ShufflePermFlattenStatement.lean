module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShufflePermFlatten
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave

@[expose] public section

open Zc.Comb
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perm_flatten_of_shuffle : ∀ {T : Type u} (us : List (List T)) (w : List T), Shuffle us w → w.Perm us.flatten := by
  exact @GlobalTheory.CompanionTheory.Comb.shuffle_perm_flatten
