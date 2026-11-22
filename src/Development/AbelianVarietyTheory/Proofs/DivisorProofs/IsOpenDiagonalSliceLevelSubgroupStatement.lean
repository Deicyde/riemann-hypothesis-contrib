module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenDiagonalSliceLevelSubgroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLOneCorner

@[expose] public section

open NumberField MeasureTheory GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.isOpen_diagonalSliceLevelSubgroup : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (hr : r ≤ a) (t : GL (Fin a) (Af E)) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → IsOpen (GlobalTheory.SliceTwo.levelSub hr t L : Set (GL (Fin (a - r)) (Af E))) := by
  first | exact @GlobalTheory.SliceTwo.isOpen_levelSub | exact GlobalTheory.SliceTwo.isOpen_levelSub | (intros; apply GlobalTheory.SliceTwo.isOpen_levelSub <;> assumption)
