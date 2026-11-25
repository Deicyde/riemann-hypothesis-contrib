module

public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.Weight

@[expose] public section

theorem Finsupp.degree_eq_card_toMultiset {α : Type} (d : α →₀ ℕ) :
    d.degree = Multiset.card (Finsupp.toMultiset d) := by
  rw [Finsupp.card_toMultiset]
  rfl
