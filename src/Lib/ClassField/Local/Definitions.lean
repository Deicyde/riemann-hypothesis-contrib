module

public import Lib.ClassField.GaloisCohomology.Cohomology
public import Lib.ClassField.Places.DecompositionCyclotomic

/-!
# The invariant and the local Artin map

For a Galois group `Γ` of `Ω` over `K` (`New.IsProGalois`), the classes in `H²(Γ, Ωˣ)` attached to
elements of `ℚ/ℤ`, and the local Artin map, defined by their characteristic properties. `H²(Γ, Ωˣ)`
is the cohomology `New.DiscreteModule.H 2` of the discrete module `New.unitsModule Γ`.

* `New.unitsModule`: `Ωˣ` written additively (`New.DiscreteUnits`), with the action of `Γ`, as a
  discrete module.
* `New.IsClassOfInvariant`, `New.Cohomology.classOfInvariant`: the map from `ℚ/ℤ` to `H²(Γ, Ωˣ)`
  normalised on unramified cyclic classes.
* `New.IsLocalArtin`, `New.localArtin`: the local Artin map, defined by duality with the cyclic
  classes `New.DiscreteModule.cyclicClass`, and its version on the completion of a number field at
  a prime.

Several objects are chosen by `epsilon` from their characteristic property.

## Relation to the literature

Known; see `Lib.ClassField.Local.ArtinMap` for sources.
-/

@[expose] public section

noncomputable section

namespace New

open NumberField Units DiscreteModule

section UnitsModule

variable (Γ : Type) [Group Γ] [TopologicalSpace Γ] {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  [MulSemiringAction Γ Ω] [hΓ : IsProGalois Γ K Ω]

/-- The multiplicative group Ω^×, written additively, as a discrete module with its continuous
action of Γ. -/
abbrev unitsModule : DiscreteModule ℤ Γ :=
  of (unitsRep (Γ := Γ) (Ω := Ω)) <|
    -- the orbit map of each unit is locally constant
    continuous_prod_of_discrete_right.2 fun x ↦
      ((isLocallyConstant_smul x.val).desc (fun g ↦ unitsRep g x) Units.val
        Units.val_injective).continuous

end UnitsModule

variable (Γ K : Type) {Ω : Type} [Group Γ] [Field K] [Field Ω] [Algebra K Ω]
  [MulSemiringAction Γ Ω] (A : ValuationSubring Ω) [TopologicalSpace Γ] [hΓ : IsProGalois Γ K Ω]

/-! ### The class of an invariant -/

/-- The property that a map `b : ℚ/ℤ → H²(Γ, Ωˣ)` sends `r` to the class of invariant `r`. First,
`b` is injective. Second, let the continuous character `χ : Γ → ℚ/ℤ` vanish on the inertia group
of `A`, let `φ` be a Frobenius element for `q = residueCard K A`, the number of elements of the
residue field, and let the invariant `w` of `Ωˣ` have normalised order `ordRat K A w = n`; then
`cyclicClass χ w = n • b (χ φ)`. -/
def IsClassOfInvariant (b : QZ →+ (unitsModule Γ (K := K) (Ω := Ω)).H 2) : Prop :=
  Function.Injective b ∧
  ∀ χ : QZChar Γ,
    (∀ g ∈ inertiaGroup Γ A, (χ : Γ → QZ) g = 0) →
    ∀ φ : Γ, IsFrob A (residueCard K A) φ →
    ∀ (w : (unitsRep (Γ := Γ) (Ω := Ω)).invariants) (n : ℤ),
      ordRat K A (w : DiscreteUnits Ω) = n →
      (unitsModule Γ (K := K) (Ω := Ω)).cyclicClass χ w = n • b ((χ : Γ → QZ) φ)

/-- A chosen additive map `ℚ/ℤ → H²(Γ, Ωˣ)` with the property `New.IsClassOfInvariant`; when such a
map exists, it sends `r` to the class of invariant `r`. See
`New.Cohomology.isClassOfInvariant_classOfInvariant_of_exists`, and for local fields
`New.IsLocalGalois.isClassOfInvariant_classOfInvariant`. -/
def Cohomology.classOfInvariant : QZ →+ (unitsModule Γ (K := K) (Ω := Ω)).H 2 :=
  Classical.epsilon (IsClassOfInvariant Γ K A)

/-- `New.Cohomology.classOfInvariant` has the property `New.IsClassOfInvariant` as soon as some map
has it. -/
lemma Cohomology.isClassOfInvariant_classOfInvariant_of_exists
    (h_exists : ∃ b : QZ →+ (unitsModule Γ (K := K) (Ω := Ω)).H 2, IsClassOfInvariant Γ K A b) :
    IsClassOfInvariant Γ K A (Cohomology.classOfInvariant Γ K A) :=
  Classical.epsilon_spec h_exists

/-! ### The local Artin map -/

/-- The property that the homomorphism `f` from `Lˣ` to the topological abelianisation of `Γ`
satisfies `classOfInvariant (χ (f x)) = -cyclicClass χ x` for every continuous character
`χ : Γ → ℚ/ℤ` and every `x` in `Lˣ`, where `x` is viewed as an invariant of `Ωˣ`, and `χ (f x)` is
the value at `f x` of `QZChar.abelianLift χ`, the map induced by `χ` on the topological
abelianisation. -/
def IsLocalArtin {L : Type*} [Field L] [Algebra L Ω] [SMulCommClass Γ L Ω]
    (f : Lˣ →* TopologicalAbelianization Γ) : Prop :=
  ∀ (χ : QZChar Γ) (x : Lˣ),
    Cohomology.classOfInvariant Γ K A (QZChar.abelianLift χ (f x)).toAdd =
      -(unitsModule Γ (K := K) (Ω := Ω)).cyclicClass χ
        (DiscreteUnits.ofBase Γ Ω (Additive.ofMul x))

variable {K} [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

/-- The local Artin map at `v`: a chosen homomorphism from the units of the completion
`v.adicCompletion K` of `K` at `v` to the abelianised decomposition group of `A`, whose
restriction to `Kˣ` satisfies `New.IsLocalArtin` over the fixed field of the decomposition group;
unspecified if there is none (see `New.isLocalArtin_localArtin_comp_of_exists` and
`New.IsPlaceOver.isLocalArtin_localArtin`). -/
def localArtin : (v.adicCompletion K)ˣ →* TopologicalAbelianization (decompGroup Γ A) :=
  Classical.epsilon fun f : (v.adicCompletion K)ˣ →* TopologicalAbelianization (decompGroup Γ A) ↦
    IsLocalArtin (decompGroup Γ A) (fixedFieldOf (decompGroup Γ A)) A
      (f.comp (map (algebraMap K (v.adicCompletion K)).toMonoidHom))

/-- The restriction of `New.localArtin Γ A v` to `Kˣ` has its defining property as soon as the
restriction of some homomorphism has it. -/
lemma isLocalArtin_localArtin_comp_of_exists
    (h_exists : ∃ f : (v.adicCompletion K)ˣ →* TopologicalAbelianization (decompGroup Γ A),
      IsLocalArtin (decompGroup Γ A) (fixedFieldOf (decompGroup Γ A)) A
        (f.comp (map (algebraMap K (v.adicCompletion K)).toMonoidHom))) :
    IsLocalArtin (decompGroup Γ A) (fixedFieldOf (decompGroup Γ A)) A
      ((localArtin Γ A v).comp (map (algebraMap K (v.adicCompletion K)).toMonoidHom)) :=
  Classical.epsilon_spec h_exists

end New
