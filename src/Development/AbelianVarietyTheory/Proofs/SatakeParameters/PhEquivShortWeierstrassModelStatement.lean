module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhEquivShortWeierstrassModel
public import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phEquiv_shortWeierstrassModel : Formalism.L2.KerInert.BeCob.PhTie := by
  exact @GlobalTheory.ShortModelTie.phTie
