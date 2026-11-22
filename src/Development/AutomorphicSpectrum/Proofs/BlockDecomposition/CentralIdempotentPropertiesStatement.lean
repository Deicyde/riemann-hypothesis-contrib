module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralIdempotentProperties
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll

@[expose] public section

open ReciprocityTheory.Ty.Fin

theorem _root_.GlobalTheory.T.central_idempotent_properties : ReciprocityTheory.Ty.Fin.St.ZIdemFacts := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.zIdemFacts | exact GlobalTheory.CompanionTheory.TyFin.zIdemFacts | (intros; apply GlobalTheory.CompanionTheory.TyFin.zIdemFacts <;> assumption)
