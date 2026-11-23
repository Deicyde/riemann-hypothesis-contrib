module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLatticeDenominatorHeightBoundProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulIntSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatInvariantUnderIntegralLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatSupportBoundedDenominators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCharacterTrivialOnSmallIdeles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLevelConductorCompatible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualLatticeBoundedDenominator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicityLevelHeightBound

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.ThetaDenom

open Formalism.UG in
theorem transport_denom : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (e : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) ≃ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)),
    ∃ C : ℝ, ∀ (g : GL (Fin n) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)), ∃ N : ℕ, 0 < N ∧
      (N : ℝ) ≤ C * ((heightGL F g : ℝ) * heightGL F h) ∧
      ∀ (M : ℕ) (y : Fin n × Fin d → AF F), IsMulInt F (M * N) y →
        IsMulInt F M (e ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, y) * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ)).1 ∧
        IsMulInt F M (e ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, y) * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ)).2 :=
  @GlobalTheory.ThetaLevel.transport_denom

end GlobalTheory.ThetaDenom

end
