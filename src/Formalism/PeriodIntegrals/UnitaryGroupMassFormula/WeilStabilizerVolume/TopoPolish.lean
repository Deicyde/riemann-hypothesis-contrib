module

public import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoPolish

@[expose] public section

noncomputable section

namespace PI.VolStabW.TopoPolish

open Topology TopologicalSpace Set

theorem polish_of_lcsc (Y : Type) [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [SecondCountableTopology Y] : PolishSpace Y := by
  exact PI.VolStabS.TopoPolish.polish_of_lcsc Y

end PI.VolStabW.TopoPolish
