module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingTheoremPhiModulesExactTriple
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents

@[expose] public section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.liftingTheorem_phiModules_exact_triple : GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Lifting := by
  first | exact @GlobalTheory.InertiaEigenvalues.lifting_along_exact_triple | exact GlobalTheory.InertiaEigenvalues.lifting_along_exact_triple | (intros; apply GlobalTheory.InertiaEigenvalues.lifting_along_exact_triple <;> assumption)
