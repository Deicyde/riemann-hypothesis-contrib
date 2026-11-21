module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ElementaryDivisorsExistDiscretelyValued
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elementaryDivisors_exist_discretelyValued : Smith := by
  exact @GlobalTheory.InertZeta.elementaryDivisors_exist_discretely_valued
