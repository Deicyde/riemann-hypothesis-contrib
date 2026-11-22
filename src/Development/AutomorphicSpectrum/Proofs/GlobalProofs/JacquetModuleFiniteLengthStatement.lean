module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible

@[expose] public section


theorem _root_.GlobalTheory.T.jacquet_module_finite_length : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetFiniteLength k := by
  first | exact @GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength | exact GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength | (intros; apply GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength <;> assumption)
