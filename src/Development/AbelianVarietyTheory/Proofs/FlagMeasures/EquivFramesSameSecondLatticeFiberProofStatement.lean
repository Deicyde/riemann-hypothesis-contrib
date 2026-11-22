module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivFramesSameSecondLatticeFiberProof
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

@[expose] public section


theorem _root_.GlobalTheory.T.equivFramesSameSecondLatticeFiber_proof : GlobalTheory.TypeAsm.FibC := by
  first | exact @GlobalTheory.TypeAsm.FibProof.fibC | exact GlobalTheory.TypeAsm.FibProof.fibC | (intros; apply GlobalTheory.TypeAsm.FibProof.fibC <;> assumption)
