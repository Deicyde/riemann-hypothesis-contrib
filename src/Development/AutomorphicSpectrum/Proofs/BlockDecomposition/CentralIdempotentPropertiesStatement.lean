module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralIdempotentProperties
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll

@[expose] public section

open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_idempotent_properties : ReciprocityTheory.Ty.Fin.St.ZIdemFacts := by
  exact @GlobalTheory.CompanionTheory.TyFin.zIdemFacts
