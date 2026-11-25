module

public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

@[expose] public section

theorem IsLocalRing.isUnit_add_of_isUnit_of_not_isUnit {R : Type*} [CommRing R] [IsLocalRing R] {u m : R}
    (hu : IsUnit u) (hm : ¬ IsUnit m) : IsUnit (u + m) := by
  by_contra h
  have h1 : u + m ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h
  have h2 : m ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hm
  have h3 : u ∈ IsLocalRing.maximalIdeal R := by
    have := Ideal.sub_mem _ h1 h2
    simpa using this
  exact (IsLocalRing.mem_maximalIdeal _).mp h3 hu
