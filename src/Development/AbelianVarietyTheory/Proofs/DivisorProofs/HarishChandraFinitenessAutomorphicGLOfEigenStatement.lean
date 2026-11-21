module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFinitenessAutomorphicGLOfEigen
public import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandra_finiteness_automorphic_GL_of_eigen : GlobalTheory.HCF.CoreFiniteGL → GlobalTheory.Published.AutomorphicFormsFiniteGL := by
  exact @GlobalTheory.HCF.automorphicFormsFiniteGL_of_core
