module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueSequenceHolds
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

theorem _root_.GlobalTheory.T.residue_sequence_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ResSeq k := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.resSeq | exact GlobalTheory.CompanionTheory.BZRes.resSeq | (intros; apply GlobalTheory.CompanionTheory.BZRes.resSeq <;> assumption)
