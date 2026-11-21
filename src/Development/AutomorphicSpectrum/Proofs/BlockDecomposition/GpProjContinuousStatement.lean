module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjContinuous
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirProjEqOneOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gpProj_continuous : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), Continuous (gpProj k m j) := by
  exact @GlobalTheory.CompanionTheory.BZMir.continuous_gpProj
