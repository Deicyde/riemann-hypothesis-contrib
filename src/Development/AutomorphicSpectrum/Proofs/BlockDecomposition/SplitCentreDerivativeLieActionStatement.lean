module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreDerivativeLieAction
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin

@[expose] public section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_centre_derivative_lie_action : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (g : GA E a) (s : ℝ), HasDerivAt (fun s : ℝ => φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a s)) ((lie E a (oneL E a) φ).1 (g * GlobalTheory.UnitaryBC.splitCentre E a s)) s := by
  exact @GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre
