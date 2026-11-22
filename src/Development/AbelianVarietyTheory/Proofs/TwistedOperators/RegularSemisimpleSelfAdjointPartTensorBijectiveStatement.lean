module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleSelfAdjointPartTensorBijective
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

@[expose] public section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.regularSemisimple_selfAdjointPart_tensor_bijective : GlobalTheory.RegSS.PlusTensorBijective := by
  first | exact @GlobalTheory.RegSS.plusTensorBijective | exact GlobalTheory.RegSS.plusTensorBijective | (intros; apply GlobalTheory.RegSS.plusTensorBijective <;> assumption)
