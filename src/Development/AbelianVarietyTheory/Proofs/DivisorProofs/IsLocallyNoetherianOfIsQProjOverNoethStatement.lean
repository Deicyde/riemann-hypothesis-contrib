module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyNoetherianOfIsQProjOverNoeth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyNoetherian_of_isQProjOver_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (f : X ⟶ Sp R), IsQProjOver f → IsLocallyNoetherian X := by
  exact @GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth
