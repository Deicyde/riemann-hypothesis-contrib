module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReducedBasisBoundedTypeOfInstance
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair

@[expose] public section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

theorem _root_.GlobalTheory.T.existsReducedBasisBoundedType_of_instance : ∀ I : AutInst, RedBasis I := by
  first | exact @GlobalTheory.CuspGeo.redBasis_holds | exact GlobalTheory.CuspGeo.redBasis_holds | (intros; apply GlobalTheory.CuspGeo.redBasis_holds <;> assumption)
