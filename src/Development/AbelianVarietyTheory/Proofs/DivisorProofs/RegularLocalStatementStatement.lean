module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularLocalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl

@[expose] public section

open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.RegularLocalStatement : RegLocSt := by
  exact @GlobalTheory.DetHT.RegLoc.main
