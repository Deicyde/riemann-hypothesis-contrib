module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericIsomorphismProductModels
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

-- c189: restore Model.prod for incomplete imports.
open CategoryTheory Limits MonoidalCategory AlgebraicGeometry in
open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
run_cmd
  unless (← Lean.getEnv).contains `GlobalTheory.SS.Model.prod do
    let prodName := Lean.mkIdent `_root_.GlobalTheory.SS.Model.prod
    Lean.Elab.Command.elabCommand (← `(
      private noncomputable def $prodName:ident
          {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]
          {A A' : Over (Sp K)} (M : GlobalTheory.SS.Model R A)
          (N : GlobalTheory.SS.Model R A') : GlobalTheory.SS.Model R (A ⊗ A') where
        Y := M.Y ⊗ N.Y
        e := (Functor.Monoidal.μIso (Over.pullback (spMap (algebraMap R K))) M.Y N.Y).symm ≪≫
          tensorIso M.e N.e
        smooth := by
          have := M.smooth
          have := N.smooth
          show Smooth (pullback.fst _ _ ≫ M.Y.hom)
          infer_instance
        sep := by
          have := M.sep
          have := N.sep
          show IsSeparated (pullback.fst _ _ ≫ M.Y.hom)
          infer_instance
        qc := by
          have := M.qc
          have := N.qc
          show QuasiCompact (pullback.fst _ _ ≫ M.Y.hom)
          infer_instance))


theorem _root_.GlobalTheory.T.generic_isomorphism_product_models : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A A' B B' : Over (Sp K)) [IsIntegral A.left] [IsIntegral (A ⊗ B).left] (M : Model R A) (M' : Model R A') (N : Model R B) (N' : Model R B') (f : A ≅ A') (Θ : A ⊗ B ⟶ A' ⊗ B'), M.Irr → M'.Irr → N.Irr → N'.Irr → Θ ≫ fst A' B' = fst A B ≫ f.hom → GenIso (M.prod N) (M'.prod N') Θ → GenIso M M' f.hom := by
  first | exact @GlobalTheory.SS.GenProj.genIso_of_prod | exact GlobalTheory.SS.GenProj.genIso_of_prod | (intros; apply GlobalTheory.SS.GenProj.genIso_of_prod <;> assumption)
