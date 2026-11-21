module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenCuspidalCharsByRegularCharsProof
public import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters

@[expose] public section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.greenCuspidalCharsByRegularChars_proof : GlobalTheory.Published.GreenRegularCharacters := by
  exact @GlobalTheory.greenRegularCharacters_holds
