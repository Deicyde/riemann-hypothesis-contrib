module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SecondCountableFiniteAdelicUnitaryPoints
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

@[expose] public section

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.secondCountable_finiteAdelicUnitaryPoints : ∀ (I : AutInst), SecondCountableTopology I.Gf := by
  first | exact @GlobalTheory.CongTop.secondCountable_finiteAdelicPoints | exact GlobalTheory.CongTop.secondCountable_finiteAdelicPoints | (intros; apply GlobalTheory.CongTop.secondCountable_finiteAdelicPoints <;> assumption)
