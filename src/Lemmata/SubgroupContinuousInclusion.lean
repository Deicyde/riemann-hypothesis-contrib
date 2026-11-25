module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Constructions

@[expose] public section

variable {G : Type*} [Group G] [TopologicalSpace G]

theorem Subgroup.continuous_inclusion {K K' : Subgroup G} (hK : K' ≤ K) :
    Continuous (Subgroup.inclusion hK) :=
  continuous_subtypeVal.subtype_mk _
