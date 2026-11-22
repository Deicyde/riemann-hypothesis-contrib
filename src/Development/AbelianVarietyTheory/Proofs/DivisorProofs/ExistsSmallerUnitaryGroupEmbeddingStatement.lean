module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallerUnitaryGroupEmbedding
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl

theorem _root_.GlobalTheory.T.exists_smaller_unitary_group_embedding : GlobalTheory.SatakeWeyl.EmbExists := by
  first | exact @GlobalTheory.SatakeWeyl.embExists | exact GlobalTheory.SatakeWeyl.embExists | (intros; apply GlobalTheory.SatakeWeyl.embExists <;> assumption)
