module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Per GlobalTheory.Prism

namespace GlobalTheory.Published

/-- A form of the classification of lattices in crystalline Galois representations by prismatic
`F`-crystals, for a finite extension of `ℚ_[l]`, stated as essential surjectivity and full
faithfulness.

Proposed reference:
[B. Bhatt and P. Scholze, *Prismatic F-crystals and crystalline Galois representations*
(Theorem 5.6, stated in the introduction as Theorem 1.2)][bhatt_scholze2023], which allows any
complete discretely valued field of mixed characteristic with perfect residue field. The encoding
of prismatic `F`-crystals used here should be compared with Definition 4.1 of that paper.
This reference is a reader's proposal and has not been checked by a mathematician. -/
def BhattScholzeIntegral : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P₀ : Obj l ↥(OL K)) (e : P₀.A ≃+* Ainf l), IsAinf K P₀ e →
    (∀ (P : LocPrime l) (AI : LocAinf l P), IsStd P AI →
      ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
        [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V]
        (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ),
        (∀ x, Continuous fun g => ρ g x) → IsCrys (P.PD K) ρ →
        ∃ (E : FCrys l ↥(OL K))
          (j : E.M P₀ →ₛₗ[(inclW l).comp e.toRingHom] (WCb l ⊗[ℤ_[l]] ↥L.T)),
          Realises K E P₀ e ↥L.T (fun g => actT L g) j) ∧
    (∀ (T T' : Type) [AddCommGroup T] [Module ℤ_[l] T] [AddCommGroup T'] [Module ℤ_[l] T']
      (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (ρ' : ↥(GK K) → (T' →ₗ[ℤ_[l]] T'))
      (E E' : FCrys l ↥(OL K))
      (j : E.M P₀ →ₛₗ[(inclW l).comp e.toRingHom] (WCb l ⊗[ℤ_[l]] T))
      (j' : E'.M P₀ →ₛₗ[(inclW l).comp e.toRingHom] (WCb l ⊗[ℤ_[l]] T')),
      Realises K E P₀ e T ρ j → Realises K E' P₀ e T' ρ' j' →
      ∀ f : T →ₗ[ℤ_[l]] T', (∀ g x, f (ρ g x) = ρ' g (f x)) →
        ∃! u : FHom E E', ∀ x, j' (u.u P₀ x) = f.lTensor (WCb l) (j x))

end GlobalTheory.Published
