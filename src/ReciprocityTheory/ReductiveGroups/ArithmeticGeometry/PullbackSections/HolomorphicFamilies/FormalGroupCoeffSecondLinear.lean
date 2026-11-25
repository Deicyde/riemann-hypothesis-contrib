module

import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CoeffSingleLawAdd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Mathlib.Order.CompletePartialOrder
import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries

@[expose] public section

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA

section Lin

variable {R : Type} [CommRing R] {d : ℕ}


theorem coeff_lin_ev {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS R m d)
    (q : Fin n × Fin d) :
    coeff (Finsupp.single q 1) (ev a f) =
      ∑ p : Fin m × Fin d, coeff (Finsupp.single p 1) f * coeff (Finsupp.single q 1) (a p.1 p.2) := by
  unfold ev
  exact GlobalTheory.FormalCalc.coeff_single_subst (a := fun p : Fin m × Fin d => a p.1 p.2)
    (fun p => ha p.1 p.2) f q

theorem coeff_X_single {n : ℕ} (q p : Fin n × Fin d) :
    coeff (Finsupp.single q 1) (X p : PS R n d) = if q = p then 1 else 0 :=
  GlobalTheory.FormalCalc.coeff_single_X q p

theorem formal_group_coeff_second_linear (G : FGLaw R d) (i l : Fin d) :
    coeff (Finsupp.single ((1 : Fin 2), l) 1) (G.F i) = if l = i then 1 else 0 := by
  apply GlobalTheory.FormalCalc.coeff_law_snd <;> assumption

theorem formal_group_coeff_first_linear (G : FGLaw R d) (i l : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), l) 1) (G.F i) = if l = i then 1 else 0 :=
  GlobalTheory.FormalCalc.coeff_law_fst G i l

end Lin

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
