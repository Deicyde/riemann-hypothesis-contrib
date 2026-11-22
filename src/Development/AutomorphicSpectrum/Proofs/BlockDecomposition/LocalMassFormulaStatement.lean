module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMassFormula
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal

@[expose] public section

open PositivityTheory.Rg.Mass

theorem _root_.GlobalTheory.T.local_mass_formula : LocMass := by
  first | exact @GlobalTheory.CompanionTheory.SW.LocBin.locMass | exact GlobalTheory.CompanionTheory.SW.LocBin.locMass | (intros; apply GlobalTheory.CompanionTheory.SW.LocBin.locMass <;> assumption)
