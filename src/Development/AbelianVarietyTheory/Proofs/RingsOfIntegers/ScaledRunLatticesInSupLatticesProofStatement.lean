module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledRunLatticesInSupLatticesProof
public import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop

theorem _root_.GlobalTheory.T.scaledRunLattices_in_supLattices : ScaledLatticesInSupLattices := by
  first | exact @GlobalTheory.PlaceTop.scaledRunLatticesInSupLattices_proof | exact GlobalTheory.PlaceTop.scaledRunLatticesInSupLattices_proof | (intros; apply GlobalTheory.PlaceTop.scaledRunLatticesInSupLattices_proof <;> assumption)
