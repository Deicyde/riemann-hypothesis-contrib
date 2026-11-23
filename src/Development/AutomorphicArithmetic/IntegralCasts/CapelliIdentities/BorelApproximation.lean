module

public import Mathlib

@[expose] public section

namespace UpperTheory.Reformulated.B.BorelApproximation

@[reducible] noncomputable def Pl (E : Type) [Field E] [NumberField E] : Type :=
  IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)

@[reducible] noncomputable def GLw {E : Type} [Field E] [NumberField E] (n : ℕ) (w : Pl E) :
    Type :=
  GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w)

theorem aux3 (k : Type) [Field k] : SubsemiringClass (Subring k) k :=
  inferInstance

theorem aux4 (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] :
    IsLocalRing (ValuativeRel.valuation k).integer :=
  inferInstance

noncomputable def blk {α n : Type} {m : α → Type} (e : (a : α) × m a ≃ n) (i : n) : α :=
  (e.symm i).fst

theorem aux6 (R : Type) [CommRing R] {α n : Type} {m : α → Type}
    [LinearOrder α] [Fintype n] [DecidableEq n] (e : (a : α) × m a ≃ n)
    {x y : GL n R}
    (hx : x ∈ {g : GL n R | g.val.BlockTriangular (blk e)})
    (hy : y ∈ {g : GL n R | g.val.BlockTriangular (blk e)}) :
    x * y ∈ {g : GL n R | g.val.BlockTriangular (blk e)} :=
  Matrix.BlockTriangular.mul hx hy

theorem aux7 (R : Type) [CommRing R] {α n : Type} {m : α → Type}
    [LinearOrder α] [Fintype n] [DecidableEq n] (e : (a : α) × m a ≃ n) :
    (1 : GL n R) ∈ {g : GL n R | g.val.BlockTriangular (blk e)} :=
  Matrix.blockTriangular_one

theorem aux8 (R : Type) [CommRing R] {α n : Type} {m : α → Type}
    [LinearOrder α] [Fintype n] [DecidableEq n] (e : (a : α) × m a ≃ n)
    {x : GL n R}
    (hx : x ∈ {g : GL n R | g.val.BlockTriangular (blk e)}) :
    x⁻¹ ∈ {g : GL n R | g.val.BlockTriangular (blk e)} := by
  have hx : Matrix.BlockTriangular (x : Matrix n n R) (blk e) := hx
  let := x.invertible
  change Matrix.BlockTriangular ((x⁻¹ : GL n R) : Matrix n n R) (blk e)
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hx

noncomputable def parab (R : Type) [CommRing R] {α n : Type} {m : α → Type}
    [LinearOrder α] [Fintype n] [DecidableEq n] (e : (a : α) × m a ≃ n) : Subgroup (GL n R) where
  carrier := {g : GL n R | g.val.BlockTriangular (blk e)}
  mul_mem' := aux6 R e
  one_mem' := aux7 R e
  inv_mem' := aux8 R e

noncomputable def points (n : Type) : ((_ : n) × Unit) ≃ n :=
  Equiv.sigmaUnique n fun _ => Unit

noncomputable def borel (R : Type) [CommRing R] (n : Type) [Fintype n] [DecidableEq n]
    [LinearOrder n] : Subgroup (GL n R) :=
  parab R (points n)

noncomputable def iwahori (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] :
    Subgroup (GL n k) :=
  Subgroup.map
    (Matrix.GeneralLinearGroup.map (n := n) (algebraMap (ValuativeRel.valuation k).integer k))
    (Subgroup.comap
      (Matrix.GeneralLinearGroup.map (n := n)
        (IsLocalRing.residue (ValuativeRel.valuation k).integer))
      (borel (IsLocalRing.ResidueField (ValuativeRel.valuation k).integer) n))

@[reducible] noncomputable def complRel {F : Type} [Field F] [NumberField F]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ValuativeRel (p.adicCompletion F) :=
  ValuativeRel.ofValuation
    (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ)))

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
private theorem exists_near {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (NumberField.RingOfIntegers F)) (x : adicCompletion F p)
    (hx : Valued.v x ≤ 1) :
    ∃ a : NumberField.RingOfIntegers F,
      Valued.v (x - algebraMap _ (adicCompletion F p) a) < 1 := by
  have hb : {y : adicCompletion F p | Valued.v (y - x) < 1} ∈ nhds x := by
    rw [Valued.mem_nhds]
    refine ⟨1, fun y hy => ?_⟩
    simpa using hy
  obtain ⟨k, hk⟩ := (denseRange_algebraMap F p).mem_nhds hb
  have hk : Valued.v (algebraMap F (adicCompletion F p) k - x) < 1 := hk
  have hv : ∀ y : F, Valued.v (algebraMap F (adicCompletion F p) y) = p.valuation F y :=
    fun y => valuedAdicCompletion_eq_valuation' p y
  have hk1 : p.valuation F k ≤ 1 := by
    rw [← hv, ← sub_add_cancel (algebraMap F (adicCompletion F p) k) x]
    exact Valuation.map_add_le _ hk.le hx
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer p hk1 1
  refine ⟨a, ?_⟩
  rw [← hv, map_sub, ← IsScalarTower.algebraMap_apply, Units.val_one] at ha
  rw [Valuation.map_sub_swap, ← sub_add_sub_cancel _ (algebraMap F (adicCompletion F p) k)]
  exact Valuation.map_add_lt _ ha hk

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
private theorem finite_residue {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    Finite (IsLocalRing.ResidueField (adicCompletionIntegers F p)) := by
  have hfin : Finite (NumberField.RingOfIntegers F ⧸ p.asIdeal) :=
    p.asIdeal.finiteQuotientOfFreeOfNeBot p.ne_bot
  have hmax : ∀ y : adicCompletionIntegers F p, Valued.v y.1 < 1 →
      IsLocalRing.residue _ y = 0 := fun y hy => by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact hy.ne
  let φ : NumberField.RingOfIntegers F →+* IsLocalRing.ResidueField (adicCompletionIntegers F p) :=
    (IsLocalRing.residue _).comp (algebraMap _ _)
  have hker : ∀ a ∈ p.asIdeal, φ a = 0 := fun a ha => by
    refine hmax _ ?_
    rw [algebraMap_adicCompletionIntegers_apply, valuedAdicCompletion_eq_valuation']
    exact (valuation_lt_one_iff_mem p a).2 ha
  refine Finite.of_surjective (Ideal.Quotient.lift p.asIdeal φ hker) fun z => ?_
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨a, ha⟩ := exists_near p x.1 x.2
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  rw [Ideal.Quotient.lift_mk, eq_comm, ← sub_eq_zero]
  have := hmax (x - algebraMap _ _ a) ha
  rwa [map_sub] at this

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
private theorem locCompact {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    LocallyCompactSpace (adicCompletion F p) := by
  have h := (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    (K := adicCompletion F p)).2
    ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (adicCompletionIntegers F p)),
      finite_residue p⟩
  exact locallyCompact_of_proper

theorem zero_contDiffOn_supported {F : Type} [Field F] [NumberField F]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    letI := complRel p
    IsNonarchimedeanLocalField (p.adicCompletion F) := by
  let := complRel p
  have : (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have : IsValuativeTopology (p.adicCompletion F) :=
    IsValuativeTopology.of_mem_nhds_zero_iff_vle
      (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ)))
      (fun {s} => Valued.is_topological_valuation s)
  have := locCompact p
  have : ValuativeRel.IsNontrivial (p.adicCompletion F) :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ)))).2 inferInstance
  exact {}

noncomputable def iwGL {E : Type} [Field E] [NumberField E] (n : ℕ) (w : Pl E) :
    Subgroup (GLw n w) :=
  letI := complRel w
  haveI := zero_contDiffOn_supported w
  iwahori (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w) (Fin n)

open scoped Classical in
noncomputable def dcos {E : Type} [Field E] [NumberField E] (n : ℕ) (w : Pl E)
    (t y : GLw n w) : ℂ :=
  if ∃ x ∈ iwGL n w, ∃ z ∈ iwGL n w, y = x * t * z then 1 else 0

theorem dcos_left {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {m : ℕ}
    {w : Pl E} (t k g : GLw m w) (hk : k ∈ iwGL m w) :
    dcos m w t (k * g) = dcos m w t g := by
  unfold dcos
  refine congrArg (fun P : Prop => @ite ℂ P (Classical.propDecidable P) 1 0) (propext ⟨?_, ?_⟩)
  · rintro ⟨x, hx, z, hz, h⟩
    refine ⟨k⁻¹ * x, mul_mem (inv_mem hk) hx, z, hz, ?_⟩
    rw [mul_assoc k⁻¹, mul_assoc k⁻¹, ← h, inv_mul_cancel_left]
  · rintro ⟨x, hx, z, hz, h⟩
    refine ⟨k * x, mul_mem hk hx, z, hz, ?_⟩
    rw [h, mul_assoc k, mul_assoc k]

end UpperTheory.Reformulated.B.BorelApproximation
