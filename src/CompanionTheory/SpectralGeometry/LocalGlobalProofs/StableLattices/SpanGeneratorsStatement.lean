module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SpanGenerators
public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

@[expose] public section

open CompanionTheory.Bmu

theorem _root_.GlobalTheory.T.SpanGenerators : SpanG := by
  first | exact @GlobalTheory.CompanionTheory.BmuSpan.spanG | exact GlobalTheory.CompanionTheory.BmuSpan.spanG | (intros; apply GlobalTheory.CompanionTheory.BmuSpan.spanG <;> assumption)
