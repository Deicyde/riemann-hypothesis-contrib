module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubringEqOK
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subring_eq_OK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ∃ R : Subring A.K, (R : Set A.K) = A.OK := by
  exact @GlobalTheory.JR.Et.OK_isSubring
